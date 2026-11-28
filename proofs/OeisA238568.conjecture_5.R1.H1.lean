import OMAReductions.R_OeisA238568_conjecture_5_R1

/-! Exact prime counts and prime witnesses in the finite range. -/

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

namespace OMA.PackedPrimeCensus

open Finset
open OMA.PackedConvolution OMA.SquareCountPilot
open OMA.PrimePopulation OMA.PrimeProgression

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

end OMA.PackedPrimeCensus

namespace OMA.PrimeCountSums

open OMA.PrimePopulation OMA.PrimeProgression OMA.PackedPrimeCensus

def rowSlot (record : ℕ) : ℕ := record % 2^24

def rowCount (record : ℕ) : ℕ := record / 2^24

def packedEvent (data i : ℕ) : ℕ := (data >>> (45*i)) % 2^45

private def rankEntry (base anchor data i : ℕ) : ℕ × ℕ :=
  let row := packedEvent data i
  let offset := rowSlot row-base
  (offset, offset-(rowCount row-anchor))

private def rankRows (base anchor data length : ℕ) : List (ℕ × ℕ) :=
  (List.range length).map (rankEntry base anchor data)

private def increasingTail : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b::rest => decide (a<b) && increasingTail b rest

private theorem increasingTail_sound {a : ℕ} {items : List ℕ} (ok : increasingTail a items = true) :
    List.Pairwise (· < ·) (a::items) := by
  induction items generalizing a with
  | nil => simp
  | cons b rest ih =>
    simp only [increasingTail,Bool.and_eq_true_iff,decide_eq_true_eq] at ok
    have tail := ih ok.2
    refine List.pairwise_cons.mpr ⟨?_,tail⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl|hj
    · exact ok.1
    · exact ok.1.trans ((List.pairwise_cons.mp tail).1 j hj)

private def increasing : List ℕ → Bool
  | [] => true
  | a::items => increasingTail a items

private theorem increasing_nodup {items : List ℕ} (ok : increasing items = true) : items.Nodup := by
  cases items with
  | nil => simp
  | cons a items => exact (increasingTail_sound ok).imp (fun h => ne_of_lt h)

private def rankGuard (lane base width anchor data i : ℕ) : Prop :=
  let row := packedEvent data i
  let offset := rowSlot row-base
  base ≤ rowSlot row ∧ offset ≤ width ∧ anchor ≤ rowCount row ∧
    rowCount row-anchor ≤ offset ∧ (rankEntry base anchor data i).2 < 2^lane

private instance (lane base width anchor data i : ℕ) : Decidable (rankGuard lane base width anchor data i) := by
  unfold rankGuard
  infer_instance

def fastPage (ps : List ℕ) (lane depth base width anchor data length : ℕ) : Prop :=
  let rows := rankRows base anchor data length
  increasing (rows.map Prod.fst) = true ∧
    (List.range length).all (fun i => decide (rankGuard lane base width anchor data i)) = true ∧
    matchLanes lane (laneCounts lane depth width (fastComposite ps base width)) rows

instance (ps : List ℕ) (lane depth base width anchor data length : ℕ) :
    Decidable (fastPage ps lane depth base width anchor data length) := by
  unfold fastPage
  infer_instance

theorem fastPage_sound {ps : List ℕ} {bound lane depth base width anchor data length : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hwidth : width < 2^depth) (hlane : 0 < lane) (hdepth : 2^depth < 2^lane)
    (hcap : 2*(base+width) ≤ (bound+1)^2) (hrank : oddCount base = anchor)
    (valid : fastPage ps lane depth base width anchor data length) :
    ∀ i < length, oddCount (rowSlot (packedEvent data i)) = rowCount (packedEvent data i) := by
  intro i hi
  let row := packedEvent data i
  let slots := rowSlot row
  let count := rowCount row
  let offset := slots-base
  let word := OMA.PrimeProgression.composite ps depth base width
  obtain ⟨ascending,checks,same⟩ := valid
  have unique := increasing_nodup ascending
  have guard (j : ℕ) (hj : j < length) : rankGuard lane base width anchor data j :=
    of_decide_eq_true (List.all_eq_true.mp checks j (List.mem_range.mpr hj))
  obtain ⟨above,hfit,hadjust,hentry,_⟩ := guard i hi
  change base ≤ slots at above
  change offset ≤ width at hfit
  change anchor ≤ count at hadjust
  change count-anchor ≤ offset at hentry
  have member : rankEntry base anchor data i ∈ rankRows base anchor data length :=
    List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have fit (q : ℕ × ℕ) (hq : q ∈ rankRows base anchor data length) : q.2 < 2^lane := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    exact (guard j (List.mem_range.mp hj)).2.2.2.2
  have hvalue := matchLanes_sound member unique fit same
  have hcounts := laneCounts_sound (fastComposite ps base width) hlane hwidth.le hdepth hfit
  change laneDigit lane (laneCounts lane depth width (fastComposite ps base width)) offset =
    offset-(count-anchor) at hvalue
  have pop : population offset word = offset-(count-anchor) := by
    have h := hcounts.symm.trans hvalue
    rw [fastComposite_eq (fun p hp => (roster p hp).1.pos) depth base width] at h
    exact h
  have hlocal := sliceOdd_exact roster complete hwidth hcap (left:=0) (span:=offset) (by simpa using hfit)
  simp only [Nat.add_zero] at hlocal
  have hslice : sliceOdd word 0 offset = offset-population offset word := by
    unfold sliceOdd
    rw [Nat.shiftRight_zero,prefixPop_exact (depth_bound offset)]
  have hadd : oddCount slots = oddCount base + Nat.count (fun i => (2*(base+i)+1).Prime) offset := by
    unfold oddCount
    conv_lhs => rw [show slots=base+offset by dsimp [offset]; omega]
    rw [Nat.count_add]
  change oddCount slots = count
  rw [hadd,← hlocal,hslice,pop,hrank]
  omega

end OMA.PrimeCountSums

namespace OMA.PrimeCountSums

open OMA.PrimePopulation

private def primes : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem roster_eq : primes = OMA.PrimeSieveBase.smallPrimes 5000 70 := by decide +kernel

private theorem roster_prime : ∀ p ∈ primes, p.Prime ∧ p%2=1 := by
  intro p hp
  rw [roster_eq] at hp
  exact ⟨OMA.PrimeSieveBase.prime_of_mem_smallPrimes (by decide) hp,
    by unfold OMA.PrimeSieveBase.smallPrimes OMA.PrimeSieveBase.checks at hp
       simp only [List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at hp
       exact hp.2.1.2⟩

private theorem roster_complete : ∀ p ≤ 5000, p.Prime → p%2=1 → p ∈ primes := by
  rw [roster_eq]
  intro p hp hprime hodd
  exact OMA.PrimeSieveBase.mem_smallPrimes hp hprime hodd

private def pageSize : ℕ := 64

private def GoodPage (data : ℕ) : Prop :=
  ∀ i < pageSize, oddCount (rowSlot (packedEvent data i)) = rowCount (packedEvent data i)

private theorem padded_page {data length : ℕ} (fit : data < 2^(45*length))
    (good : ∀ i < length, oddCount (rowSlot (packedEvent data i)) = rowCount (packedEvent data i)) :
    GoodPage data := by
  intro i _
  by_cases hi : i < length
  · exact good i hi
  · have waste : data / 2^(45*i) = 0 := by
      apply Nat.div_eq_of_lt
      exact fit.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 45 (by omega)))
    simp [packedEvent,Nat.shiftRight_eq_div_pow,waste,rowSlot,rowCount,oddCount]

private theorem cons_good_page {page : ℕ} {pages : List ℕ} (head : GoodPage page)
    (tail : ∀ q ∈ pages, GoodPage q) : ∀ q ∈ page::pages, GoodPage q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact head
  · exact tail q hq

private theorem lookup_good_page {pages : List ℕ} (valid : ∀ q ∈ pages, GoodPage q) (i : ℕ) :
    GoodPage (pages.getD i 0) := by
  induction pages generalizing i with
  | nil => exact padded_page (length:=0) (data:=0) (by decide) (by omega)
  | cons page pages ih =>
    cases i with
    | zero => exact valid page (by simp)
    | succ i => exact ih (fun q hq => valid q (List.mem_cons_of_mem _ hq)) i

private def eventAt (pages : List ℕ) (i : ℕ) : ℕ :=
  packedEvent (pages.getD (i/pageSize) 0) (i%pageSize)

private theorem eventAt_sound {pages : List ℕ} (valid : ∀ q ∈ pages, GoodPage q) (i : ℕ) :
    oddCount (rowSlot (eventAt pages i)) = rowCount (eventAt pages i) :=
  lookup_good_page valid (i/pageSize) (i%pageSize) (Nat.mod_lt _ (by decide))

private def GoodWitness (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime ((n^2).primeCounting + (k*n).primeCounting - 1)

private def checkWitness (pages : List ℕ) (fastPrime : ℕ → Bool) (n row : ℕ) : Bool :=
  let k := row%128
  let sqEvent := eventAt pages (row/128%16384)
  let knEvent := eventAt pages (row/2097152)
  decide (2≤n ∧ 0<k ∧ k<n ∧ rowSlot sqEvent=(n^2+1)/2 ∧ rowSlot knEvent=(k*n+1)/2) &&
    fastPrime (1+rowCount sqEvent+rowCount knEvent)

private theorem checkWitness_sound {pages : List ℕ} {fastPrime : ℕ → Bool}
    (pagesGood : ∀ q ∈ pages, GoodPage q) (primeSound : ∀ p, fastPrime p=true → p.Prime)
    {n row : ℕ} (ok : checkWitness pages fastPrime n row=true) : GoodWitness n := by
  let k := row%128
  let sqEvent := eventAt pages (row/128%16384)
  let knEvent := eventAt pages (row/2097152)
  simp only [checkWitness,Bool.and_eq_true_iff,decide_eq_true_eq] at ok
  obtain ⟨⟨hn,hk,lt,hs,hkn⟩,hp⟩ := ok
  have hsq : 2 ≤ n^2 := Nat.le_trans (by decide : 2≤2^2) (Nat.pow_le_pow_left hn 2)
  have hprod : 2 ≤ k*n := by
    calc
      2 ≤ n := hn
      _ ≤ k*n := by simpa using Nat.mul_le_mul_right n (show 1≤k by omega)
  have sq := eventAt_sound pagesGood (row/128%16384)
  have kn := eventAt_sound pagesGood (row/2097152)
  change oddCount (rowSlot sqEvent) = rowCount sqEvent at sq
  change oddCount (rowSlot knEvent) = rowCount knEvent at kn
  change rowSlot sqEvent=(n^2+1)/2 at hs
  change rowSlot knEvent=(k*n+1)/2 at hkn
  change fastPrime (1+rowCount sqEvent+rowCount knEvent)=true at hp
  refine ⟨k,hk,lt,?_⟩
  rw [oddCount_eq_primeCounting hsq,oddCount_eq_primeCounting hprod,←hs,←hkn,sq,kn]
  have arithmetic : 1+rowCount sqEvent+(1+rowCount knEvent)-1 = 1+rowCount sqEvent+rowCount knEvent := by omega
  rw [arithmetic]
  exact primeSound _ hp

private def checkWitnesses (pages : List ℕ) (fastPrime : ℕ → Bool) (n word : ℕ) : ℕ → Bool
  | 0 => true
  | length+1 => checkWitness pages fastPrime n (word%2^35) &&
      checkWitnesses pages fastPrime (n+1) (word/2^35) length

private theorem checkWitnesses_sound {pages : List ℕ} {fastPrime : ℕ → Bool}
    (pagesGood : ∀ q ∈ pages, GoodPage q) (primeSound : ∀ p, fastPrime p=true → p.Prime)
    {first word length : ℕ} (verified : checkWitnesses pages fastPrime first word length = true) :
    ∀ n, first ≤ n → n < first+length → GoodWitness n := by
  induction length generalizing first word with
  | zero => omega
  | succ length ih =>
    rw [checkWitnesses,Bool.and_eq_true_iff] at verified
    intro n hlo hhi
    by_cases eq : n=first
    · subst n
      exact checkWitness_sound pagesGood primeSound verified.1
    · exact ih verified.2 n (by omega) (by omega)

private theorem join_witness {a b c : ℕ}
    (left : ∀ n, a≤n → n<b → GoodWitness n) (right : ∀ n, b≤n → n<c → GoodWitness n) :
    ∀ n, a≤n → n<c → GoodWitness n := by
  intro n hlo hhi
  by_cases hb : n<b
  · exact left n hlo hb
  · exact right n (by omega) hhi

private def page0Data : ℕ := 0x168000338000b4000198000580000c60002b0000620001480002e80009c0001640004e0000b0000270000570001300002b000098000154000480000a20002300004e000110000258000840001280004200009200021000048000108000238000840001180003e0000880001f0000430000f0000208000780001000003a00007e0001d00003d0000e80001d0000700000e00003800006e0001b0000360000d00001a0000640000cc00030000064000180000310000b80001780005c0000b80002e00005a0001600002c0000a8000148000500000940002600004800012000023000088000108000440000800002200003e0001000001e0000780000e00003c00006c0001c0000320000c0000150000580000a00002c00004c000140000240000a000011000048000078000200000380001000001a0000800000c0000380000580001c0000280000c000012000050000080000180000280000800000c0000200000400000000001

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page0Checked : PLift (fastPage primes 8 7 0 103 0 page0Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page0 (anchor : OMA.PrimePopulation.oddCount 0 = 0) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page0Data i)) =
      rowCount (packedEvent page0Data i) := by
  exact fastPage_sound (width:=103) (bound:=5000) (base:=0) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page0Checked.down

private theorem page0Good : GoodPage page0Data := by
  have anchor : oddCount 0 = 0 := by simp [oddCount]
  exact (page0 anchor)

private def page1Data : ℕ := 0x2b00007200015800038c000ac0001c4000550000e00002a00006e80014c000364000a40001b0000510000d60002800006900013c0003440009e00019c0004e0000cc000270000658001380003280009a0001900004d0000c700026000063000130000314000960001840004b0000c1000258000600001240002f400092000176000480000ba0002400005c8001200002e00008e00016c000470000b50002380005a0001140002c00008a00015e000440000ae0002180005500010800029c0008200014a000410000a4000208000518001040002880008000013c0003e00009a0001e80004a0000f0000248000780001220003c00008f0001e0000470000e800023000072000114000390000880001a8000400000d40001f8000680000fa0003400007c0001a00003d8000d00001e8000660000f0000320000760001900003a8000bc0001c40005e0000e00002e00006e000170000368000b80001ac0005c0000d40002d000069

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page1Checked : PLift (fastPage primes 8 7 103 125 45 page1Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page1 (anchor : OMA.PrimePopulation.oddCount 103 = 45) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page1Data i)) =
      rowCount (packedEvent page1Data i) := by
  exact fastPage_sound (width:=125) (bound:=5000) (base:=103) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page1Checked.down

private theorem page1Good : GoodPage page1Data := by
  have anchor : oddCount 103 = 45 := by exact page0Good 63 (by decide)
  exact (page1 anchor)

private def page2Data : ℕ := 0x420000bc00020c0005d0001040002e600081000170000400000b70002000005b4001000002d80007f00016b0003f0000b28001f8000590000fc0002c60007d0001620003d8000ac8001ec000558000f40002a6000790001520003c0000a80001d4000518000ea000288000720001400003900009f8001c80004f8000e4000278000710001390003780009a0001b80004c8000dc0002600006c00012c000358000950001a800049c000d2000246000690001220003400009000019c000474000cc000236000650001170003200008a00019000044c000c80002240006300010f00031000087000188000430000c40002120006200010800031000083800188000418000c200020a0006000010400030000081000180000404000c0000200000600000ff0002e80007c0001740003dc000b80001ea0005c0000f40002d80007900016c0003c4000b60001e00005a0000ef0002d0000760001680003ac000b40001d4000570000e5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page2Checked : PLift (fastPage primes 9 8 228 148 86 page2Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page2 (anchor : OMA.PrimePopulation.oddCount 228 = 86) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page2Data i)) =
      rowCount (packedEvent page2Data i) := by
  exact fastPage_sound (width:=148) (bound:=5000) (base:=228) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page2Checked.down

private theorem page2Good : GoodPage page2Data := by
  have anchor : oddCount 228 = 86 := by exact page1Good 63 (by decide)
  exact (page2 anchor)

private def page3Data : ℕ := 0x5e00011b8002ec0008cc00174000462000b900022e0005c0001148002e00008a000168000442000b300021e0005980010e0002c400084c00160000424000af00020d000570001058002b80008280015c000412000ad000207000568001030002ac00080800156000400000a90001fc000540000fd0002a00007e40014e0003ea000a50001ef000528000f70002900007a4001460003cc000a20001e5000510000f2000284000788001420003c2000a10001e0000500000ee00028000076c001400003b40009e0001d60004f0000ea800274000750001380003a00009b0001cb0004c8000e100026400070000132000378000980001bb0004a8000d98002500006b80012200034a000910001a4000480000d0800240000680001180003320008a000194000450000c90002280006400011400031e0008900018d000448000c60002200006240011000031000088000187000440000c30002180005fc0010c0002fc0008500017c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page3Checked : PLift (fastPage primes 9 8 376 191 132 page3Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page3 (anchor : OMA.PrimePopulation.oddCount 376 = 132) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page3Data i)) =
      rowCount (packedEvent page3Data i) := by
  exact fastPage_sound (width:=191) (bound:=5000) (base:=376) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page3Checked.down

private theorem page3Good : GoodPage page3Data := by
  have anchor : oddCount 376 = 132 := by exact page2Good 63 (by decide)
  exact (page3 anchor)

private def page4Data : ℕ := 0x6f800164800378000b14001bc000584000de0002c10006e800160000374000af8001ba00057a000dd0002bc0006e00015d000370000ad0001b400055c000da0002ad0006c000154000360000a98001b0000548000d80002a30006c000150800360000a78001b000053a000d800029c0006c00014d800360000a68001ae00052e000d70002960006b80014a800358000a50001aa00051e000d500028e0006a00014600034c000a2c001a2000510000d0000285000678001420003300009f0001980004f6000cc0002790006600013b00032c0009cc001960004e4000ca00026f000650001370003280009b0001920004d2000c80002670006380013280031c0009900018c0004c6000c60002620006300013080031400097c001880004ba000c400025a0006180012b00030c000954001840004a6000c2000252000608001280003000009300017e00048e000be0002450005f0001210002f00008f800178000474000bc000239

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page4Checked : PLift (fastPage primes 9 8 567 146 188 page4Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page4 (anchor : OMA.PrimePopulation.oddCount 567 = 188) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page4Data i)) =
      rowCount (packedEvent page4Data i) := by
  exact fastPage_sound (width:=146) (bound:=5000) (base:=567) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page4Checked.down

private theorem page4Good : GoodPage page4Data := by
  have anchor : oddCount 567 = 188 := by exact page3Good 63 (by decide)
  exact (page4 anchor)

private def page5Data : ℕ := 0x850001ad000424000d50002100006a20010700034f000830001a7000418000d340020c00069400106000349000830001a2800418000d1000204000678001020003380008100019b800408000cd8002040006680010200033300080800198800404000cc00020200065c0010000032d000800001958003f8000ca4001fa00064c000fd0003250007d8001918003e8000c80001f200063c000f900031d0007c80018d8003e4000c64001f2000630000f80003170007b80018a0003dc000c48001ea000618000f3000308000798001838003c8000c18001e4000608000f10003020007880017f0003c0000bf4001e00005f8000ef0002f90007780017b0003bc000bd4001dc0005e6000ee0002f1000770001780003b8000bbc001dc0005dc000ed0002eb000760001750003a0000b88001ce0005be000e70002dd0007380016e00039c000b68001cc0005b2000e60002d700071800169000388000b3c001c400059c000e00002ca

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page5Checked : PLift (fastPage primes 9 8 713 145 223 page5Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page5 (anchor : OMA.PrimePopulation.oddCount 713 = 223) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page5Data i)) =
      rowCount (packedEvent page5Data i) := by
  exact fastPage_sound (width:=145) (bound:=5000) (base:=713) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page5Checked.down

private theorem page5Good : GoodPage page5Data := by
  have anchor : oddCount 713 = 223 := by exact page4Good 63 (by decide)
  exact (page5 anchor)

private def page6Data : ℕ := 0x990001fb0004c4000fd4002620007e8001300003ef000978001f68004bc000fa80025c0007d20012e0003e8000968001f38004ac000f8c002540007c20012a0003de000948001ee0004a0000f68002500007b0001280003d6000940001ea8004a0000f440024e00079e001260003cd000930001e6000498000f2000248000782001240003bd000918001dd800488000ee40024200076c001210003b4000908001d9800484000ec800242000762001200003b0000900001d7800478000ea80023c0007520011b0003a50008d8001d1800468000e7400234000738001190003990008c8001cb800464000e580023200072a001180003930008c0001c880045c000e300022c00070e001150003820008a8001c000044c000df4002260006f80011200037b000890001bd000444000ddc002220006e800111000372000880001b7800440000db80021e0006d80010e000368000870001b3800434000d98002180006c40010c000361

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page6Checked : PLift (fastPage primes 9 8 858 156 266 page6Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page6 (anchor : OMA.PrimePopulation.oddCount 858 = 266) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page6Data i)) =
      rowCount (packedEvent page6Data i) := by
  exact fastPage_sound (width:=156) (bound:=5000) (base:=858) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page6Checked.down

private theorem page6Good : GoodPage page6Data := by
  have anchor : oddCount 858 = 266 := by exact page5Good 63 (by decide)
  exact (page6 anchor)

private def page7Data : ℕ := 0xb18002570005880012b0002c000094e0015f0004a6000af800252800574001278002ba00093a0015c00049a000ae00024c800570001260002b200092400158000491000ab80024600055c001228002ae00090800155000482000aa800240800554001200002a40008ee00152000475000a880023a0005440011cc0029c0008d60014e000468000a7000233800534001190002980008c20014c000460000a480022a000520001148002900008a200148000450000a30002268005180011300028c00089600146000447000a300022280051800110c0028a00087c0014500043d000a280021e0005100010dc0028800086c0014100042d000a00002160005000010ac0027c00084c0013e0004220009e8002100004f000107c0027800083a0013c00041a0009b8002080004dc0010340026a00080e001350004060009a0002008004d0001000002680007fe001340003fc000998001fd8004cc000fe4002660007f0001330003f7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page7Checked : PLift (fastPage primes 9 8 1014 184 306 page7Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page7 (anchor : OMA.PrimePopulation.oddCount 1014 = 306) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page7Data i)) =
      rowCount (packedEvent page7Data i) := by
  exact fastPage_sound (width:=184) (bound:=5000) (base:=1014) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page7Checked.down

private theorem page7Good : GoodPage page7Data := by
  have anchor : oddCount 1014 = 306 := by exact page6Good 63 (by decide)
  exact (page7 anchor)

private def page8Data : ℕ := 0xc78002ae00063c00156c0031c000ab40018e000559000c70002ac00063800155c0031a000aaa0018c000554000c60002a980063000154800318000aa00018b00054e000c50002a600062400152800310000a9000188000547000c38002a200061400150000308000a7c0018200053a000c100029c8006040014d800302000a680017f000531000bf0002978005f80014b8002fa000a540017d000528000bc80028a8005e4001448002f0000a200017700050f000bb8002868005dc00142c002ec000a0e00176000502000bb0002808005d40013f8002e60009f4001730004f8000b880027a8005c00013c4002e00009da0016f0004eb000b78002750005bc0013a4002de0009d00016f0004e7000b70002718005b8001388002dc0009c00016e0004dc000b700026d0005b4001354002d80009a80016c0004d2000b50002668005a8001328002d200098e001690004c6000b380025f80059c0012f0002c8000964001640004b1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page8Checked : PLift (fastPage primes 9 8 1198 174 355 page8Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page8 (anchor : OMA.PrimePopulation.oddCount 1198 = 355) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page8Data i)) =
      rowCount (packedEvent page8Data i) := by
  exact fastPage_sound (width:=174) (bound:=5000) (base:=1198) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page8Checked.down

private theorem page8Good : GoodPage page8Data := by
  have anchor : oddCount 1198 = 355 := by exact page7Good 63 (by decide)
  exact (page8 anchor)

private def page9Data : ℕ := 0xde00030d0006f000186400376000c30001ba000617000dd00030a0006e400184800372000c18001b8000608000db8003028006dc0018100036c000c04001b6000600000db0002ff8006d00017e800368000bf0001b40005f7000da0002fa8006c40017b400362000bd8001b10005ea000d88002f48006c00017980035e000bc8001ac0005db000d60002ec0006b000174400354000b96001aa0005ca000d48002e480069c0017080034e000b7c001a60005bd000d30002de0006980016e40034a000b6e001a40005b2000d20002d800068c0016b000342000b4c001a10005a4000d00002d000067c0016700033e000b360019f000598000cf8002cb8006780016580033c000b2a0019d000594000ce0002c780067000163800336000b180019a000589000cc8002c380066000160000330000afc0019800057d000cc0002be0006540015d800326000ae400193000570000c88002b300064400158c00322000ac20018f00055e

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page9Checked : PLift (fastPage primes 9 8 1372 190 399 page9Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page9 (anchor : OMA.PrimePopulation.oddCount 1372 = 399) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page9Data i)) =
      rowCount (packedEvent page9Data i) := by
  exact fastPage_sound (width:=190) (bound:=5000) (base:=1372) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page9Checked.down

private theorem page9Good : GoodPage page9Data := by
  have anchor : oddCount 1372 = 399 := by exact page8Good 63 (by decide)
  exact (page9 anchor)

private def page10Data : ℕ := 0xf3000368000798001b3c003cc000d9a001e60006ca000f3000364800790001b14003c4000d82001e10006c0000f080035f000784001af4003c0000d70001e00006b5000ef80035a00077c001ac4003be000d60001df0006ae000ef800356000778001aa0003ba000d4e001dd0006a4000ee800351800774001a88003b8000d3e001db00069e000ed80034e00076c001a6c003b6000d34001db000698000ec800349800764001a48003b2000d22001d6000689000ea800343800754001a10003aa000d06001d5000682000e900033e8007400019e00039e000ce8001cd00066f000e68003370007340019b40039a000ccc001cc000663000e600033080073000198000390000cb2001c8000656000e400032a00072000194000390000c9e001c600064a000e28003240007000018d800380000c6a001c0000633000e00003188006f80018bc0037a000c5a001bd00062c000de8003138006f400189000378000c40001bc00061d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page10Checked : PLift (fastPage primes 9 8 1562 182 444 page10Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page10 (anchor : OMA.PrimePopulation.oddCount 1562 = 444) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page10Data i)) =
      rowCount (packedEvent page10Data i) := by
  exact fastPage_sound (width:=182) (bound:=5000) (base:=1562) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page10Checked.down

private theorem page10Good : GoodPage page10Data := by
  have anchor : oddCount 1562 = 444 := by exact page9Good 63 (by decide)
  exact (page10 anchor)

private def page11Data : ℕ := 0x1098003c000084c001df800424000ef200210000774001080003b8800840001dc00041e000eda0020f00076b001070003b4800834001da00041a000eca0020d000764001060003af800828001d6400412000eac00209000755001048003aa000824001d4800412000ea20020800074d001038003a5000818001d140040c000e88002050007430010280039f800810001cf800408000e7a002020007380010100039b000804001ccc00402000e600020000072d000ff8003960007f8001cac003fa000e40001fb00071a000fd80038c8007e8001c5c003f4000e2a001fa000714000fc0003880007e0001c3c003ec000e16001f6000708000fa8003818007d4001c04003e8000dfe001f30006fe000f980037e8007c8001be4003e4000dee001f20006f6000f900037a0007c4001bcc003e0000de4001f00006f0000f80003770007b8001ba8003da000dd0001ed0006e7000f50003710007a8001b7c003d0000db6001e70006d4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page11Checked : PLift (fastPage primes 9 8 1744 176 486 page11Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page11 (anchor : OMA.PrimePopulation.oddCount 1744 = 486) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page11Data i)) =
      rowCount (packedEvent page11Data i) := by
  exact fastPage_sound (width:=176) (bound:=5000) (base:=1744) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page11Checked.down

private theorem page11Good : GoodPage page11Data := by
  have anchor : oddCount 1744 = 486 := by exact page10Good 63 (by decide)
  exact (page11 anchor)

private def page12Data : ℕ := 0x11c80040e0008e40020640047200102e002390008160011c00040a8008e000204c0046a00101c002350008080011a0004038008cc00200000462000ff4002310007f9001180003fb8008bc001fd00045e000fdc0022e0007ec001168003f48008b0001f9800458000fc80022c0007e3001160003f10008b0001f8400458000fc00022b0007dd001148003eb8008a0001f5800450000faa002270007d2001130003e8800894001f400044a000f9e002250007cb001120003e4000890001f1c00448000f8c002240007c4001120003e1000890001f0400446000f7c002230007bd001118003dd800884001ecc0043e000f580021f0007ab0010f0003d4800870001e9800438000f480021b0007a30010d0003cf800868001e7000434000f36002190007980010c8003cb800864001e5800430000f28002180007930010b8003c900085c001e440042e000f200021700078d0010b8003c6000858001e240042c000f1000213000782

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page12Checked : PLift (fastPage primes 9 8 1920 156 531 page12Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page12 (anchor : OMA.PrimePopulation.oddCount 1920 = 531) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page12Data i)) =
      rowCount (packedEvent page12Data i) := by
  exact fastPage_sound (width:=156) (bound:=5000) (base:=1920) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page12Checked.down

private theorem page12Good : GoodPage page12Data := by
  have anchor : oddCount 1920 = 531 := by exact page11Good 63 (by decide)
  exact (page12 anchor)

private def page13Data : ℕ := 0x1350004770009a80023b0004d20011d4002690008e900134000472800998002384004cc0011c0002660008df0013300046c800998002360004c60011a2002620008ce00130000462800980002310004be0011820025e0008be0012f00045e0009740022d4004b80011680025c0008b20012d8004580009640022a4004b2001150002590008a70012c800453000964002294004b2001148002580008a30012b00044d800958002268004ac001132002560008980012a80044b000950002248004a800111c00253000886001288004410009440021fc004a00010fc0025000087b0012700043b0009340021cc0049a0010e40024d000870001268004378009340021b00049a0010d00024d00086600126000432000930002188004960010bc00248000855001230004280009140021380048a0010940024300084600121800422800904002108004820010820023c0008270011e0004100008ec00207c0047400103c0023a00081d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page13Checked : PLift (fastPage primes 9 8 2076 210 569 page13Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page13 (anchor : OMA.PrimePopulation.oddCount 2076 = 569) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page13Data i)) =
      rowCount (packedEvent page13Data i) := by
  exact fastPage_sound (width:=210) (bound:=5000) (base:=2076) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page13Checked.down

private theorem page13Good : GoodPage page13Data := by
  have anchor : oddCount 2076 = 569 := by exact page12Good 63 (by decide)
  exact (page13 anchor)

private def page14Data : ℕ := 0x14b8004da000a580026c40052a001358002940009ab001498004d3800a40002684005200013380028f000999001478004cc000a380026580051a0013240028d000990001468004c6800a3000262c005180013140028b000986001448004bf000a240025e8005120012f000289000976001440004b5000a180025940050c0012c400285000960001420004af800a00002558005000012aa00280000954001400004a68009fc002520004fc00128a0027e00093f0013e00049e0009ec0024e4004f40012700027a0009370013d00049b0009e80024c8004f40012620027a0009300013c8004978009e40024b8004f200125a002780009260013b0004900009d8002474004ea001236002750009190013a00048c0009d000245c004e600122a00271000911001388004880009bc002438004de0012180026f000909001378004840009b800240c004dc0011fe0026d0008fc0013600047c0009ac0023d8004d60011ea0026a0008f0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page14Checked : PLift (fastPage primes 9 8 2286 198 618 page14Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page14 (anchor : OMA.PrimePopulation.oddCount 2286 = 618) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page14Data i)) =
      rowCount (packedEvent page14Data i) := by
  exact fastPage_sound (width:=198) (bound:=5000) (base:=2286) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page14Checked.down

private theorem page14Good : GoodPage page14Data := by
  have anchor : oddCount 2286 = 618 := by exact page13Good 63 (by decide)
  exact (page14 anchor)

private def page15Data : ℕ := 0x163800547000b18002a2400586001500002c3000a7d0016180053d000b0c0029dc005860014ec002c2000a7300160800537000b000029a40057e0014c8002bf000a610015f80052f800af0002960005780014aa002bc000a520015c800526000ae400292800572001490002b8000a440015c000521000ae00028f800570001478002b6000a380015a000519000ad00028c000566001456002b3000a2800159000512800ac800289000562001444002b1000a200015880050f800ac000287000560001436002af000a190015700050b800ab80028500055c001422002ac000a0b00156000505000ab000281c00558001404002ac000a01001558004ff800aa80027e8005520013f0002a80009f6001538004fa800a980027bc005480013d4002a30009e1001510004ee800a88002768005440013b2002a20009d80014e8004e3000a680027000053400137c002990009bc0014c8004dd800a640026e800532001372002980009b5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page15Checked : PLift (fastPage primes 9 8 2484 218 663 page15Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page15 (anchor : OMA.PrimePopulation.oddCount 2484 = 663) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page15Data i)) =
      rowCount (packedEvent page15Data i) := by
  exact fastPage_sound (width:=218) (bound:=5000) (base:=2484) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page15Checked.down

private theorem page15Good : GoodPage page15Data := by
  have anchor : oddCount 2484 = 663 := by exact page14Good 63 (by decide)
  exact (page15 anchor)

private def page16Data : ℕ := 0x1858005cd800c28002e600061400172a00309000b93001848005c9000c20002e200060c00170400306000b7f001830005bf000c10002de0006080016ee00303000b76001808005b9000bf8002db0005f40016b8002f7000b500017b0005a7000bd8002d34005e8001692002f4000b480017a0005a2800bd0002d00005e8001676002f2000b370017800059a000bc0002cc8005de001650002ee000b2500176800591000bb4002c84005d6001634002e9000b1100174800588000b90002c18005c4001600002e2000afd0017080057d000b84002be0005c20015e8002e1000af200170800578000b80002ba8005c00015d2002df000ae30016e80056f000b70002b70005b60015ae002db000ad50016d80056a000b6c002b40005b0001590002d7000ac30016a00055e000b50002ae8005a8001572002d3000ab400168800559000b44002ac0005a000155e002d0000aa90016680054f800b2c002a6800596001532002cb000a98

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page16Checked : PLift (fastPage primes 10 9 2702 269 711 page16Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page16 (anchor : OMA.PrimePopulation.oddCount 2702 = 711) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page16Data i)) =
      rowCount (packedEvent page16Data i) := by
  exact fastPage_sound (width:=269) (bound:=5000) (base:=2702) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page16Checked.down

private theorem page16Good : GoodPage page16Data := by
  have anchor : oddCount 2702 = 711 := by exact page15Good 63 (by decide)
  exact (page16 anchor)

private def page17Data : ℕ := 0x1a4800658800d240032c00069000195600348000caa001a4000654800d1c0032a00068c00194800345000ca1001a280064f000d0c0032600068600192e00343000c94001a1800649000d080032300068200191000341000c87001a0800642800d04003210006820019000033e000c740019e000637800ce80031a8006720018ce00339000c650019c800632000cdc00317c0066c0018b400335000c5900199800628800cc00031100065e0018800032c000c3a0019580061b000cac0030d0006540018620032a000c3000194800614000c980030840064c00184000323000c170019180060a000c8c00304c0064600181e00322000c0e00190800604000c8000300c0063a0017f20031d000bf70018d8005f7800c60002f88006300017c000315000bd60018a0005e8000c4c002f380062400179a00310000bc6001880005df800c38002eec006180017580030c000ba4001860005d1800c2c002e800061600173e0030b000b9d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page17Checked : PLift (fastPage primes 10 9 2971 278 779 page17Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page17 (anchor : OMA.PrimePopulation.oddCount 2971 = 779) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page17Data i)) =
      rowCount (packedEvent page17Data i) := by
  exact fastPage_sound (width:=278) (bound:=5000) (base:=2971) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page17Checked.down

private theorem page17Good : GoodPage page17Data := by
  have anchor : oddCount 2971 = 779 := by exact page16Good 63 (by decide)
  exact (page17 anchor)

private def page18Data : ℕ := 0x1bc8006c7000de4003634006f2001b1800379000d89001bc8006c2000de0003608006f0001b0000376000d7d001ba8006bc000dd40035d8006ea001aea00375000d74001ba8006b9000dd00035c0006e6001ad600371000d67001b88006b3000dc4003594006dc001ab00036d000d56001b58006a8000da8003520006d4001a8c00368000d40001b300069e000d980034ec006cc001a7200366000d37001b2000697800d900034b8006c8001a5800362000d22001b080068f800d8400346c006c0001a300035e000d16001af00068a000d74003444006b8001a1e0035a000d07001ad000682800d5c0033e8006ac0019e800356000cf3001ab000678800d580033c0006aa0019d800355000ceb001a9800671800d4c003378006a40019b400351000cd8001a800066a800d3c0033500069e0019a40034e000cd1001a6000665800d2c003320006960019840034b000cc1001a5000660000d280032f80069400197a00349000cba

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page18Checked : PLift (fastPage primes 9 8 3249 221 841 page18Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page18 (anchor : OMA.PrimePopulation.oddCount 3249 = 841) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page18Data i)) =
      rowCount (packedEvent page18Data i) := by
  exact fastPage_sound (width:=221) (bound:=5000) (base:=3249) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page18Checked.down

private theorem page18Good : GoodPage page18Data := by
  have anchor : oddCount 3249 = 841 := by exact page17Good 63 (by decide)
  exact (page18 anchor)

private def page19Data : ℕ := 0x1d4800734000ea400399c00752001ccc003a8000e60001d300072c800e9400394800748001ca0003a2000e46001d0800721000e800038fc00740001c7a003a0000e3c001d000071d000e7c0038e40073e001c700039f000e2d001cf800716000e780038a00073a001c4e0039c000e24001ce000711800e6c00388800734001c3c0039a000e1d001cd00070d000e540038300072a001c1400393000e04001c9800700800e4c0037fc00724001bf200391000df1001c88006f8000e440037b400720001bd80038f000deb001c70006f4000e380037980071c001bca0038e000de3001c60006ef800e3000376800718001bac0038b000dd2001c58006e8800e2c00374000714001b9600389000dc8001c48006e1000e200037000070e001b7800387000dbb001c28006d9800e100036c800706001b5800382000da9001c08006d2800e04003690006fc001b3a0037d000d9b001be0006cc000dec003658006f2001b2000379000d8f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page19Checked : PLift (fastPage primes 9 8 3470 218 889 page19Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page19 (anchor : OMA.PrimePopulation.oddCount 3470 = 889) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page19Data i)) =
      rowCount (packedEvent page19Data i) := by
  exact fastPage_sound (width:=218) (bound:=5000) (base:=3470) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page19Checked.down

private theorem page19Good : GoodPage page19Data := by
  have anchor : oddCount 3470 = 889 := by exact page18Good 63 (by decide)
  exact (page19 anchor)

private def page20Data : ℕ := 0x1f08007b1000f80003d78007be001eb4003de000f54001ee8007a8000f68003d0c007b4001e84003da000f40001ed00079f000f68003ce8007b2001e70003d5000f22001ea800790000f50003c68007a4001e26003d1000f0c001e8000785000f3c003c200079c001e0a003ce000f04001e600077f000f28003be800794001df2003ca000ef6001e3800775000f1c003ba00078e001dc8003c6000ee0001e300076e000f10003b6400782001d9c003c0000ecc001df800764800ef8003b100077a001d7e003bb000ebd001dd80075e000eec003aec00772001d70003b9000eb7001dc80075a800edc003abc0076a001d50003b5000ea7001da000752000ed0003a8400764001d3e003b2000e9e001d800074b800ec0003a4c0075c001d20003ae000e8e001d6800746800eb4003a180075a001d0a003ac000e84001d600073f800eac0039f000756001cf4003aa000e77001d5000739000ea40039bc00752001cdc003a9000e6d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page20Checked : PLift (fastPage primes 9 8 3688 250 937 page20Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page20 (anchor : OMA.PrimePopulation.oddCount 3688 = 937) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page20Data i)) =
      rowCount (packedEvent page20Data i) := by
  exact fastPage_sound (width:=250) (bound:=5000) (base:=3688) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page20Checked.down

private theorem page20Good : GoodPage page20Data := by
  have anchor : oddCount 3688 = 937 := by exact page19Good 63 (by decide)
  exact (page20 anchor)

private def page21Data : ℕ := 0x20d000836801068004194008340020c8004190010620020b80082e00105800415c0082c0020ac004150010530020a80082900104c00410c0082600208200410001034002070008180010340040b400814002040004090010180020380080a00101800404c008080020180040400100a0020180080400100c0040180080600200600403001001002010007ff001004003fe000802001fec003fd000fe9001fe8007ef800ff4003f78007f4001faa003f9000fd2001fc0007e7000fdc003f30007ec001f92003f5000fc5001fa8007e1800fd0003efc007e6001f78003f2000fba001f90007dc800fc8003edc007e4001f68003f1000fb2001f88007d6800fc4003eb0007e2001f54003f0000fa8001f70007d0800fb4003e6c007da001f2a003ed000f8e001f60007c5000fac003e1c007d4001f02003e7000f79001f38007bc000f98003dd0007cc001ee4003e4000f6d001f20007b5000f90003da4007c8001ecc003e3000f65

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page21Checked : PLift (fastPage primes 10 9 3938 267 993 page21Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page21 (anchor : OMA.PrimePopulation.oddCount 3938 = 993) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page21Data i)) =
      rowCount (packedEvent page21Data i) := by
  exact fastPage_sound (width:=267) (bound:=5000) (base:=3938) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page21Checked.down

private theorem page21Good : GoodPage page21Data := by
  have anchor : oddCount 3938 = 993 := by exact page20Good 63 (by decide)
  exact (page21 anchor)

private def page22Data : ℕ := 0x22e0008ca00116c004638008b600231a0045b00118c0022d0008c280115c0045e0008aa0022e40045300116a002298008b200114400456c008a20022b400450001150002260008a180112c004508008940022780044900113a0022400089b8011180044c00088c0022540044500112600222000892001110004488008860022380044300111b002208008898010fc0044400087c00221a004350010ec0021a0008748010d00043a0008680021ca004320010dc0021800086c0010bc00434c0085c00219a0042e0010cc002160008650010b000431c0085800218c0042c0010c5002160008620010ac0043080085200216c004290010b50021480085a00109400429800848002148004240010a20021180084f80108c0042780084600213a004220010980021100084b0010880042480084400211e0042200108a0021080084400108000420c0084000210400420001081002100008400010700041d0008340020e00041a00106e

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page22Checked : PLift (fastPage primes 10 9 4205 295 1050 page22Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page22 (anchor : OMA.PrimePopulation.oddCount 4205 = 1050) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page22Data i)) =
      rowCount (packedEvent page22Data i) := by
  exact fastPage_sound (width:=295) (bound:=5000) (base:=4205) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page22Checked.down

private theorem page22Good : GoodPage page22Data := by
  have anchor : oddCount 4205 = 1050 := by exact page21Good 63 (by decide)
  exact (page22 anchor)

private def page23Data : ℕ := 0x25380096c801298004b5c0094a0025a0004a30012cd00251000965801288004b28009400025840049f0012c00024f80095e80127c004af00093e0025740049e0012b80024f00095b801278004aa00093800254a0049c0012a20024d00094d001264004a580093000252600496001287002488009390012400049bc0091e0024dc0048d00126800246800933801230004998009160024c80048a0012610024500092f80121000490800902002474004810012380023f0009168011f80048a8008fc0024520047d0012220023d00090f0011e800486c008f4002430004790012110023a8009010011d4004800008e80023f8004740011fb002390008fb8011c40047c4008e00023dc0046f0011e8002378008f30011b8004790008da0023c20046c0011db002358008ec00119c004718008cc002382004660011c0002330008de0011980046dc008c800235e004630011ac002308008d400118400468c008c00023420046000119c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page23Checked : PLift (fastPage primes 10 9 4500 325 1116 page23Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page23 (anchor : OMA.PrimePopulation.oddCount 4500 = 1116) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page23Data i)) =
      rowCount (packedEvent page23Data i) := by
  exact fastPage_sound (width:=325) (bound:=5000) (base:=4500) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page23Checked.down

private theorem page23Good : GoodPage page23Data := by
  have anchor : oddCount 4500 = 1116 := by exact page22Good 63 (by decide)
  exact (page23 anchor)

private def page24Data : ℕ := 0x26c8009e5001364004f24009b0002778004d60013b90026a0009d800134c004eb8009a4002754004d10013a9002688009d4001344004e9c009a000274c004d00013a3002680009d1001340004e700099c00272a004ce001394002670009c8801338004e3800998002710004cc001384002660009c1801330004dfc009980026fa004cb001378002650009ba001324004db4009900026ce004c8001366002630009b1801314004d780098a0026b8004c4001359002618009ab00130c004d4c009860026a4004c3001351002610009a7801304004d300097c00267c004bc0013360025d0009990012e8004cc00097400265e004b900132c0025c8009958012e0004ca00096e00264a004b70013240025b8009910012d0004c6800968002630004b40013170025a00098b0012cc004c5000964002622004b200130e002590009858012c4004c200095c002604004ac0012f80025600097b8012ac004bc0009500025c2004a80012e0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page24Checked : PLift (fastPage primes 9 8 4825 241 1191 page24Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page24 (anchor : OMA.PrimePopulation.oddCount 4825 = 1191) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page24Data i)) =
      rowCount (packedEvent page24Data i) := by
  exact fastPage_sound (width:=241) (bound:=5000) (base:=4825) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page24Checked.down

private theorem page24Good : GoodPage page24Data := by
  have anchor : oddCount 4825 = 1191 := by exact page23Good 63 (by decide)
  exact (page24 anchor)

private def page25Data : ℕ := 0x291000a9200148800548000a44002a340052200151800290800a8a80148000544800a3e002a1c0051e0015070028f000a8200147800540800a380029f20051a0014f30028c000a7580145400537c00a2a0029b2005150014d80028a800a6b00144800534000a22002990005100014c700288000a6200143800530400a1c00297c0050d0014b900286000a5b00142c0052d000a12002948005080014a000283800a4b80141c00525000a0c0029220050500148b00282000a440014000051d800a000028e8004ff00146e0027e000a338013f0005190009f20028b6004f90014580027c800a290013e4005140009f000289c004f800144c0027b800a240013d80050f0009ea00286e004f400143200278800a158013c00050a0009de002848004ef00142300277800a100013b4005070009d6002820004e5001401002728009fe801394004fec009c60027da004e30013ec002710009f3001380004f80009c00027bc004dd0013d6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page25Checked : PLift (fastPage primes 10 9 5066 346 1241 page25Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page25 (anchor : OMA.PrimePopulation.oddCount 5066 = 1241) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page25Data i)) =
      rowCount (packedEvent page25Data i) := by
  exact fastPage_sound (width:=346) (bound:=5000) (base:=5066) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page25Checked.down

private theorem page25Good : GoodPage page25Data := by
  have anchor : oddCount 5066 = 1241 := by exact page24Good 63 (by decide)
  exact (page25 anchor)

private def page26Data : ℕ := 0x2b8000b508015bc005a6000ada002d140056d001688002b6800b428015b0005a0000ad6002cfe0056b00167e002b5800b3e0015ac0059e800ad4002cec0056700166e002b2000b3080159000597400ac4002cb200562001658002b0800b2800158000592800aba002c7a0055c001635002ad000b1600156000587c00aaa002c2800553001608002a8800b020015380057e400a9c002bf00054c0015f2002a6000af800153000579c00a96002bc80054b0015e0002a5000aef00152800576000a94002bac005490015d4002a3800ae800151c00573800a8a002b90005440015c5002a0000ad88014fc0056a400a7e002b500053800158f0029b800ac48014dc00561800a6e002b080053300157000299000ab68014c80055a400a62002acc0053000156200298000ab00014b800556800a5c002aa60052d00154e00296000aa40014ac00551400a52002a820052900153c00293800a9b0014940054c800a46002a5400523001529

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page26Checked : PLift (fastPage primes 10 9 5412 381 1314 page26Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page26 (anchor : OMA.PrimePopulation.oddCount 5412 = 1314) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page26Data i)) =
      rowCount (packedEvent page26Data i) := by
  exact fastPage_sound (width:=381) (bound:=5000) (base:=5412) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page26Checked.down

private theorem page26Good : GoodPage page26Data := by
  have anchor : oddCount 5412 = 1314 := by exact page25Good 63 (by decide)
  exact (page26 anchor)

private def page27Data : ℕ := 0x2de800c018016f400600800b78003000005b80017f0002db000bf68016d8005fa800b66002fbe005b30017dc002d9800bed0016c0005f4800b60002f94005b00017c4002d7000be00016b4005ef800b5a002f78005ab0017b5002d5800bd90016ac005eb800b56002f58005a70017a3002d3000bd1001694005e7400b4a002f36005a3001793002d1800bc800168c005e3000b44002f100059f00177d002cd800bb280166c005d9000b36002ec60059900175e002cb800bac001654005d3c00b22002e800058e001735002c7000b98001638005cb800b18002e4400588001719002c3000b88001614005c3c00b04002e04005800016fe002c0000b7d001600005bd000afe002dd80057c0016e0002be000b6e0015e8005b6400af4002db00057a0016d5002bb800b670015dc005b2c00aee002d90005770016c6002bb000b610015d8005b0400aec002d80005760016be002ba800b5b0015cc005ac000ae6002d5c005710016a2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page27Checked : PLift (fastPage primes 10 9 5793 354 1392 page27Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page27 (anchor : OMA.PrimePopulation.oddCount 5793 = 1392) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page27Data i)) =
      rowCount (packedEvent page27Data i) := by
  exact fastPage_sound (width:=354) (bound:=5000) (base:=5793) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page27Checked.down

private theorem page27Good : GoodPage page27Data := by
  have anchor : oddCount 5793 = 1392 := by exact page26Good 63 (by decide)
  exact (page27 anchor)

private def page28Data : ℕ := 0x309800cc800184c00662000c2600330c0061200198300309000cc100184800660000c1c0032e80060e00196e00307000cb600182800659000c140032c40060a00195c002ff800c9b8017f80064d000bf600323c005fa00191a002fb000c840017d400640800be40031e4005f20018f1002f9000c780017c80063b800be00031d4005f00018e4002f7800c718017b800638400bd80031a0005eb0018ce002f4800c620017a400630800bd0003178005e30018ae002f1800c5500178c00629800bc4003148005e000189f002ef800c4e00177000624000bb800311a005db00188a002ed800c4400176c00621800bb2003100005d7001878002eb000c3b8017580061d000baa0030e0005d2001866002e8000c3180173800616800b9c0030b2005ce001856002e6000c2700173000613400b94003090005ca001847002e4800c200017180060e000b86003058005c2001824002e1000c0f00170000606800b7c003022005be00180c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page28Checked : PLift (fastPage primes 10 9 6147 397 1469 page28Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page28 (anchor : OMA.PrimePopulation.oddCount 6147 = 1469) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page28Data i)) =
      rowCount (packedEvent page28Data i) := by
  exact fastPage_sound (width:=397) (bound:=5000) (base:=6147) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page28Checked.down

private theorem page28Good : GoodPage page28Data := by
  have anchor : oddCount 6147 = 1469 := by exact page27Good 63 (by decide)
  exact (page28 anchor)

private def page29Data : ℕ := 0x325800d5100192c006a8400c9200353400647001a9100323800d48001918006a3800c8a00351600645001a8700322800d42801910006a0000c860034f800642001a7700321000d398019000069a000c800034cc0063f001a640031f000d2e0018f800696400c7c0034b00063d001a570031e800d2a8018f000694800c7800349e0063b001a4c0031d000d258018e800692800c7400349200639001a480031b800d1d0018d80068d800c6800345e00634001a2e00319800d158018c80068a000c6400344800631001a2200318000d0d0018b800683000c5c0034140062d001a0800316000d038018b000681000c580034060062a0019fa00314000cf88018a00067b000c4c0033c4006240019da00312000ceb80188c00675400c460033a8006210019d000310800ce580187c0066f800c3c0033760061d0019b90030e800cdc0018640066b000c3200334a0061600199a0030a800ccb80185000665000c2600332400613001991

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page29Checked : PLift (fastPage primes 10 9 6544 274 1555 page29Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page29 (anchor : OMA.PrimePopulation.oddCount 6544 = 1555) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page29Data i)) =
      rowCount (packedEvent page29Data i) := by
  exact fastPage_sound (width:=274) (bound:=5000) (base:=6544) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page29Checked.down

private theorem page29Good : GoodPage page29Data := by
  have anchor : oddCount 6544 = 1555 := by exact page28Good 63 (by decide)
  exact (page29 anchor)

private def page30Data : ℕ := 0x34f000e1f001a780070f000d3a0038700069c001c360034d800e18001a680070b800d2e00384a00696001c230034b000e10801a5400708000d2a00383600693001c1600349000e07001a4800702c00d2200380a00691001c0400348000dfe001a34006fd000d1a0037e00068b001bea00345000ded801a24006f5400d100037a800687001bd000343000de3001a10006ee800d0800376e00684001bb400341000dd5001a08006ea400cfc0037360067e001b920033e800dc60019f4006e1400cfa00370800679001b7b0033c800dba8019e0006dc800cee0036d800675001b6600338800da98019b4006cc800cd000364200667001b1c00332000d8b80198c006c3800cbc0035de0065d001aee0032e000d74001970006b9400cb80035c800659001adc0032c000d6d801960006b5400cae00359e00655001acc00329800d60801944006af800ca000357a0064f001abb00327800d5d001930006abc00c9800355c0064c001aa9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page30Checked : PLift (fastPage primes 10 9 6818 412 1611 page30Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page30 (anchor : OMA.PrimePopulation.oddCount 6818 = 1611) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page30Data i)) =
      rowCount (packedEvent page30Data i) := by
  exact fastPage_sound (width:=412) (bound:=5000) (base:=6818) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page30Checked.down

private theorem page30Good : GoodPage page30Data := by
  have anchor : oddCount 6818 = 1611 := by exact page29Good 63 (by decide)
  exact (page30 anchor)

private def page31Data : ℕ := 0x377800edd001bb80076d400ddc003b68006ec001daa00375800ed4001ba800768000dce003b22006e6001d9000372800ec6801b9000762000dc8003b0a006e3001d8000371000ebe001b840075d800dbe003ae4006de001d700036e800eb4001b7000758000db6003ab6006db001d590036c800ea9001b6400753000db2003a96006d9001d4a0036a800e99001b4400748800da0003a30006ce001d1200365000e80801b2800740000d8e0039ea006c5001cee00362800e76001b1000738c00d800039ae006c0001cd40035f800e69001aec00731800d7400398a006ba001cc30035c800e60801adc0072e400d6c00395e006b5001caa00359800e50001ac800726c00d64003934006b2001c9900359000e4c001ac400725c00d5a003918006ad001c8a00355000e38801aa40071c000d480038c8006a3001c5f00351000e2d801a8800716000d440038ac006a1001c4d00350000e24801a8000712000d3e00388c0069f001c44

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page31Checked : PLift (fastPage primes 10 9 7230 380 1694 page31Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page31 (anchor : OMA.PrimePopulation.oddCount 7230 = 1694) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page31Data i)) =
      rowCount (packedEvent page31Data i) := by
  exact fastPage_sound (width:=380) (bound:=5000) (base:=7230) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page31Checked.down

private theorem page31Good : GoodPage page31Data := by
  have anchor : oddCount 7230 = 1694 := by exact page30Good 63 (by decide)
  exact (page31 anchor)

private def page32Data : ℕ := 0x3b2800ff4801d8c007f7800eb8003f640075b001fae003ab000fcc001d58007e5400eac003f1600756001f8a003aa000fc0801d4c007dfc00ea4003eee00752001f74003a7000fb4001d38007d9800e8e003ea000745001f40003a2000f9d801d04007ca000e82003e4a00740001f1e003a0000f8e801cf8007c5c00e6e003e0400737001eff0039b800f7e001cd8007bc800e6c003de000733001ee000399800f6f801cc4007b6000e5e003daa0072f001ecf00397000f67001cb8007b3000e56003d8000728001eba00393000f5b801c98007ab800e48003d3e00722001e990038e000f42801c6c007a0400e36003cfe00719001e780038b800f36001c5c0079a400e26003cb400712001e5000388800f23801c3c00790400e1c003c6c0070c001e3000384800f11001c1c00786000e06003c1000702001e0600380000efe801bfc0077e400dfa003be0006fa001de30037c000eee001bdc00776800de4003b9a006f1001dc1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page32Checked : PLift (fastPage primes 11 10 7610 559 1775 page32Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page32 (anchor : OMA.PrimePopulation.oddCount 7610 = 1775) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page32Data i)) =
      rowCount (packedEvent page32Data i) := by
  exact fastPage_sound (width:=559) (bound:=5000) (base:=7610) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page32Checked.down

private theorem page32Good : GoodPage page32Data := by
  have anchor : oddCount 7610 = 1775 := by exact page31Good 63 (by decide)
  exact (page32 anchor)

private def page33Data : ℕ := 0x3d80010af801ec000857000f5e0042aa007af002154003d60010a3001eac00851000f4e004272007a6002130003d2801096801e8c0084a000f4400423c007a200211a003cf801088801e7400843000f3a0042100079d002107003ce801082801e6c00840800f320041f0007980020f5003cb801075801e5c0083a400f2e0041d0007940020dc003c980106d801e4c00835800f240041a6007920020d2003c800105e001e3c0082ec00f1c0041680078c0020ab003c6001050001e2000825000f0e00411a0078600208a003c1801040801e0c0081fc00f040040f80078100207b003c0001039801dfc0081b800efc0040d80077e00206a003bf001032001df800818400efc0040c00077d00205d003be00102d801dec00816000ef200409c00778002044003bb80101d001dd80080d400eec00406800773002028003b8801010801dc000807c00ed60040080076b002003003b5801000001da8007ff800ed2003ff000767001ff1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page33Checked : PLift (fastPage primes 10 9 8169 374 1893 page33Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page33 (anchor : OMA.PrimePopulation.oddCount 8169 = 1893) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page33Data i)) =
      rowCount (packedEvent page33Data i) := by
  exact fastPage_sound (width:=374) (bound:=5000) (base:=8169) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page33Checked.down

private theorem page33Good : GoodPage page33Data := by
  have anchor : oddCount 8169 = 1893 := by exact page32Good 63 (by decide)
  exact (page33 anchor)

private def page34Data : ℕ := 0x407801192802020008c480100e00460c008040023000040200117f002004008bc800ffe0045cc007fb0022d6003fd801169001fe8008b3800ff2004582007f60022ba003fb00115b001fd8008ad400fec004568007f50022af003f9801153801fbc008a5000fde00451a007e8002268003f200112b001f8c00895000fc2004498007e100224a003ef80111f001f7c0088f400fbe004470007de002235003ee001116001f6000888800fae00443e007d600221a003ea801109801f5400884800fa8004422007d3002208003e80010fe001f400087e800f9e0043f0007cb0021ef003e58010f6001f2800879800f900043b8007c40021d2003e08010e1001f0400870400f8200437c007c10021b8003e08010db801ef800869400f7c004344007bc00219b003de0010cd001ee800864c00f70004316007b8002188003db8010c2801ed80085f400f6c0042f8007b600217b003da8010ba001ed00085c000f680042de007b2002166

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page34Checked : PLift (fastPage primes 10 9 8543 454 1968 page34Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page34 (anchor : OMA.PrimePopulation.oddCount 8543 = 1968) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page34Data i)) =
      rowCount (packedEvent page34Data i) := by
  exact fastPage_sound (width:=454) (bound:=5000) (base:=8543) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page34Checked.down

private theorem page34Good : GoodPage page34Data := by
  have anchor : oddCount 8543 = 1968 := by exact page33Good 63 (by decide)
  exact (page34 anchor)

private def page35Data : ℕ := 0x43480127f0021a40093d8010c80049cc008640024e500430801262002184009308010c200497a008600024b90042e8012580021700092a4010b800494e0085c0024a40042c80124c802160009240010ae00491e0085700248e0042b001245002154009218010a8004902008540024800042a00123f002140009198010a00048ca00850002462004260012258021300091140109800487e008490024300042400121680211800909c0108c004848008450024200042200120f00211000906c01086004830008430024120041e0011fd0020e4008fac010720047cc008380023e40041b8011f00020d4008f580106a0047a6008330023ca004180011e08020b0008eb0010580047540082b0023a8004148011d280209c008e680104e00473200823002389004108011c1002084008dfc010400046f200820002378004100011bb00207c008dc0010320046be0081900235e0040b0011a4802040008cd8010200046620080f00232e

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page35Checked : PLift (fastPage primes 10 9 8997 473 2063 page35Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page35 (anchor : OMA.PrimePopulation.oddCount 8997 = 2063) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page35Data i)) =
      rowCount (packedEvent page35Data i) := by
  exact fastPage_sound (width:=473) (bound:=5000) (base:=8997) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page35Checked.down

private theorem page35Good : GoodPage page35Data := by
  have anchor : oddCount 8997 = 2063 := by exact page34Good 63 (by decide)
  exact (page35 anchor)

private def page36Data : ℕ := 0x45e00134c0022dc009a180116e004d0a008b70026840045a80133d0022c40099c001162004cd0008b0002661004580013300022c00099680115c004c90008ad0026460045580131d0022a80098dc01154004c6c008a9002631004540013180022940098940114a004c3c008a500261c0045280130d00229000986001140004c100089d0026010044a0012f48022380097500111c004b9c0088e0025c4004468012df8022340096f40111a004b780088a0025b2004450012d80022240096a001110004b48008870025a1004430012ce00221000964001106004b1800882002589004408012c30021fc0095f8010fe004af00087d0025760043e8012b70021ec0095a0010f4004ac40087900255e0043c8012ad8021e0009530010ec004a88008750025410043a0012a00021cc0094ec010e6004a7400873002538004390012990021c00094a4010de004a440086e0025200043700128f8021b400945c010d6004a1200869002501

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page36Checked : PLift (fastPage primes 10 9 9470 410 2153 page36Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page36 (anchor : OMA.PrimePopulation.oddCount 9470 = 2153) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page36Data i)) =
      rowCount (packedEvent page36Data i) := by
  exact fastPage_sound (width:=410) (bound:=5000) (base:=9470) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page36Checked.down

private theorem page36Good : GoodPage page36Data := by
  have anchor : oddCount 9470 = 2153 := by exact page35Good 63 (by decide)
  exact (page36 anchor)

private def page37Data : ℕ := 0x48e00143d80246800a1d8012340050ea0091900286e0048c00143500245c00a1700122c0050b2009160028580048b00142a80245000a138012280050980091400284b0048900142080244800a1000122400507a009100028340048800141780243c00a0940121c0050460090d0028200048600140f00242000a00c0120e005000009050027f1004818013f6002408009f94011fa004f9c008fd0027c90047e0013e40023ec009f0c011ee004f70008f60027b50047b0013da0023d0009ea0011e4004f38008f1002793004780013c80023c0009e34011da004f06008ec002779004760013bc0023a0009d88011ce004eba008e40027530046f8013a2802370009cc0011b0004e3c008d500271000469001385002344009c1001192004dc4008c80026d90046380136c00231c009b5c0118e004daa008c70026d400463801368002318009b340118a004d94008c00026b10045f8013560022f8009aa00117c004d4e008bd0026a0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page37Checked : PLift (fastPage primes 10 9 9880 483 2236 page37Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page37 (anchor : OMA.PrimePopulation.oddCount 9880 = 2236) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page37Data i)) =
      rowCount (packedEvent page37Data i) := by
  exact fastPage_sound (width:=483) (bound:=5000) (base:=9880) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page37Checked.down

private theorem page37Good : GoodPage page37Data := by
  have anchor : oddCount 9880 = 2236 := by exact page36Good 63 (by decide)
  exact (page37 anchor)

private def page38Data : ℕ := 0x4cb80156400265000aad00132600556600992002aaf004c680154e00263400aa680131800552a0098b002a8f004c480154280261800a9e4013060054de00983002a6a004c080152e8025fc00a950012fc00549c0097c002a46004be00151e8025e800a8d8012f200546a00976002a2a004b800150a8025bc00a830012d00053f2009660029f1004b30014f800259000a758012c400539a009610029cc004ac8014d280256400a690012ae00534400956002998004aa0014c680252800a560012940052ae00949002954004a40014a800252000a53c0128a00528c00945002945004a180149c80250800a4d0012820052600093f0029220049f0014900024f800a4700127a0052220093900290a0049b8014800024dc00a3fc012660051de009330028ec004988014708024bc00a370012560051920092a0028c60049480145f8024a400a2f80124e005164009250028a00049280144d80249000a25c012440051220091d002880

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page38Checked : PLift (fastPage primes 11 10 10363 589 2332 page38Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page38 (anchor : OMA.PrimePopulation.oddCount 10363 = 2332) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page38Data i)) =
      rowCount (packedEvent page38Data i) := by
  exact fastPage_sound (width:=589) (bound:=5000) (base:=10363) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page38Checked.down

private theorem page38Good : GoodPage page38Data := by
  have anchor : oddCount 10363 = 2332 := by exact page37Good 63 (by decide)
  exact (page38 anchor)

private def page39Data : ℕ := 0x50380167c00281000b3b8013f8005980009fa002cb7004fd00165b0027e000b2a8013ea005934009f5002c91004f90016448027c800b218013e4005908009f2002c83004f88016400027bc00b1f0013da0058de009ed002c6c004f60016350027a800b184013d20058c0009e7002c56004f200162780279000b130013c4005880009e0002c38004ed80161380276c00b088013b600583e009db002c1b004ed80160c00276400b050013aa00580c009d5002c04004ea00160080274c00afdc013a40057e4009d2002bf0004e78015f000273800af680138a005754009c5002ba8004e18015d000270c00ae7401380005712009ba002b74004dc0015ae8026e000ad640136c0056a4009b5002b4d004da8015a48026c800ad0c01354005640009a7002b19004d300158a80269800ac500134a005622009a3002b08004d080157f80267400abc4013360055c80099b002ae1004cc80156c00266000ab50013300055a000997002acb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page39Checked : PLift (fastPage primes 11 10 10952 560 2455 page39Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page39 (anchor : OMA.PrimePopulation.oddCount 10952 = 2455) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page39Data i)) =
      rowCount (packedEvent page39Data i) := by
  exact fastPage_sound (width:=560) (bound:=5000) (base:=10952) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page39Checked.down

private theorem page39Good : GoodPage page39Data := by
  have anchor : oddCount 10952 = 2455 := by exact page38Good 63 (by decide)
  exact (page39 anchor)

private def page40Data : ℕ := 0x52b00174080295400b9e8014a2005cd000a4e002e5f0052680172e80293400b9640149a005cac00a4d002e540052600172900293000b94001498005c9400a4a002e400052380171c80291c00b8e00148c005c6c00a46002e2f0052300171600291000b89801482005c3600a3e002e110051e8017070028d400b7c00146a005bd800a35002deb0051a0016f30028cc00b79001466005bc400a33002de1005198016ef0028c800b75401464005ba400a31002dcc005178016e18028b800b6e40145c005b6800a2d002daf005168016d58028a800b66401454005b2c00a26002d8c005128016c080289000b60001446005afc00a22002d7c005100016b900288000b5b00143e005ad200a1f002d640050f0016ad00287800b5580143c005aaa00a1d002d530050d8016a800286000b5080142e005a7800a14002d280050980169180284c00b48001424005a3800a12002d1a0050900168c00283c00b4300141c005a1400a0b002d06

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page40Checked : PLift (fastPage primes 10 9 11512 393 2567 page40Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page40 (anchor : OMA.PrimePopulation.oddCount 11512 = 2567) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page40Data i)) =
      rowCount (packedEvent page40Data i) := by
  exact fastPage_sound (width:=393) (bound:=5000) (base:=11512) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page40Checked.down

private theorem page40Good : GoodPage page40Data := by
  have anchor : oddCount 11512 = 2567 := by exact page39Good 63 (by decide)
  exact (page40 anchor)

private def page41Data : ℕ := 0x562001860002af800c2800157800612600abc0030900055c001840002ae000c1fc015700060fa00ab800307b0055b00183a002ad000c1ac015680060d200aaf00304a00557801824002ab800c1080155c00607e00aac0030390055600181b002aa800c0c80155400606200aa900302b00554001812802a9400c03001546005fe800aa2002ff20054d8017e8002a6800bf2c01532005f9000a99002fc50054c8017e1002a6400befc01532005f7c00a98002fbc0054a8017d8002a5000beb001526005f4c00a8d002f88005460017c1802a3000be0001516005ee600a88002f5a005430017a8802a1400bd2401506005e7e00a7f002f290053e8017908029f000bc68014f2005e2800a75002f080053a0017820029cc00bc04014e6005e0000a6f002eed0053780177600299c00bb30014cc005d8800a65002ebb0053200175a80298c00bacc014c0005d5400a5f002ea70052e80175000297000ba68014b6005d1c00a57002e84

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page41Checked : PLift (fastPage primes 11 10 11905 575 2646 page41Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page41 (anchor : OMA.PrimePopulation.oddCount 11905 = 2646) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page41Data i)) =
      rowCount (packedEvent page41Data i) := by
  exact fastPage_sound (width:=575) (bound:=5000) (base:=11905) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page41Checked.down

private theorem page41Good : GoodPage page41Data := by
  have anchor : oddCount 11905 = 2646 := by exact page40Good 63 (by decide)
  exact (page41 anchor)

private def page42Data : ℕ := 0x5a000199a802d0000cccc0167400663400b3700330c0059a801980002cc800cbe0016620065d600b2a0032c700594801960802ca400cb000165000657600b220032a100591001950002c8400ca780164000653400b1d0032880058e001942802c6400c9c0016300064d800b1500325d0058a80192b802c3800c8d80161800645a00b0800321600583001908802c1000c81c0160200640000afd0031f40057e8018f9002be800c77c015f20063b000af90031ce0057c8018e5802be400c710015ec00637600af60031ba0057a0018db002bcc00c6c8015e000634200aef00319a005750018c0802b9c00c5d0015ce0062e000ae300316a005718018b4802b8c00c5a0015c60062cc00ae3003161005718018ac002b8400c540015b800627200adc0031350056d001897802b5800c480015aa00623800ad50031150056a80188a002b4400c41c0159e0061f200ace0030f600566801876802b2800c3800159000619800ac40030c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page42Checked : PLift (fastPage primes 11 10 12480 629 2756 page42Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page42 (anchor : OMA.PrimePopulation.oddCount 12480 = 2756) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page42Data i)) =
      rowCount (packedEvent page42Data i) := by
  exact fastPage_sound (width:=629) (bound:=5000) (base:=12480) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page42Checked.down

private theorem page42Good : GoodPage page42Data := by
  have anchor : oddCount 12480 = 2756 := by exact page41Good 63 (by decide)
  exact (page42 anchor)

private def page43Data : ℕ := 0x5e0801aec002f0400d74c01782006ba400bc00035cc005df801ae5002ef800d71c0177c006b8a00bbb0035b8005dd801ad8802ee000d6a80176a006b2a00bb3003591005d9801ac7002ec000d5f001760006af200bb0003575005d8001aba002eb800d59c0175a006ac800bad003563005d6001aac002e8c00d4b401746006a5400b9c0034f2005cd801a78002e6400d398017300069c400b970034df005cb001a6e002e4000d3040172000698000b8d0034af005c6001a53002e2400d2700171200693000b8700348f005c3001a44002e0800d1e0016fa0068d000b7d003466005be801a32002de800d140016ee00687600b7700343a005bb001a1b802dcc00d0c4016e200685800b7000342a005b8001a13802da800d068016cc00680400b650033ff005b10019f2802d8400cf7c016bc00678e00b5e0033c6005ad0019d7002d6000ce98016a600672600b4c003369005a48019ae802d0c00cd140168400668400b4200333f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page43Checked : PLift (fastPage primes 11 10 13109 675 2880 page43Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page43 (anchor : OMA.PrimePopulation.oddCount 13109 = 2880) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page43Data i)) =
      rowCount (packedEvent page43Data i) := by
  exact fastPage_sound (width:=675) (bound:=5000) (base:=13109) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page43Checked.down

private theorem page43Good : GoodPage page43Data := by
  have anchor : oddCount 13109 = 2880 := by exact page42Good 63 (by decide)
  exact (page43 anchor)

private def page44Data : ℕ := 0x623801c3200311400e178018880070b600c430038540061f801c200030f000e0c40187200704000c3900381e0061c001c0e0030dc00e0640186c00702600c360038100061a801c070030cc00e00c01864006ffa00c2d0037ef00613801bee00308800df2401844006f9000c210037c70060d801bd700306800dea401832006f4800c1500378900608001bbc00303800ddb401818006eb800c0b00374b00603001b9e00301000dcc001808006e5c00c0400372700601801b9080300c00dc8001802006e3000bfe003708005fe801b80802ff000dbec017f8006de800bfc0036f3005fd001b73802fd000db3c017e4006d8800bf20036c3005f7801b5a002fa800da70017d2006d3000be9003696005f2001b43002f9000da10017c4006cf200be1003675005f0801b35002f8400d9a4017b8006ca800bdc003651005ed801b28002f6000d920017ac006c8000bd500363d005e5801b0c002f2c00d85c0178e006c0000bc60035fd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page44Checked : PLift (fastPage primes 11 10 13784 652 3009 page44Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page44 (anchor : OMA.PrimePopulation.oddCount 13784 = 3009) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page44Data i)) =
      rowCount (packedEvent page44Data i) := by
  exact fastPage_sound (width:=652) (bound:=5000) (base:=13784) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page44Checked.down

private theorem page44Good : GoodPage page44Data := by
  have anchor : oddCount 13784 = 3009 := by exact page43Good 63 (by decide)
  exact (page44 anchor)

private def page45Data : ℕ := 0x65c801d6c0032e000eb440196a00759400cb2003abf00658001d590032bc00eaac0195e00754e00cae003aa400656001d4e8032b000ea640195400750c00caa003a8500654001d3b8032a000e9d8019500074ea00ca5003a6b00652801d3080329400e980019440074b000c9d003a420064e801d1f00326800e8880192c00742600c96003a0e0064a001d0400325000e818019260073f000c8b0039ca00645001ce400321800e6f80190600734400c8200399600640801cc900320000e63c018f60072ee00c7b0039760063d001cb70031d400e588018e80072ae00c7400395500638801ca48031c400e520018e000728a00c6d00393500635001c908031a400e474018ce00721e00c6400390700631801c8000318000e3d0018bc0071d600c590038d00062c801c6600315800e2f8018ac00717000c500038a800628001c4f80314000e2740189c00711c00c4e00388d00626801c4380313000e208018900070e400c4800386d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page45Checked : PLift (fastPage primes 11 10 14436 628 3143 page45Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page45 (anchor : OMA.PrimePopulation.oddCount 14436 = 3143) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page45Data i)) =
      rowCount (packedEvent page45Data i) := by
  exact fastPage_sound (width:=628) (bound:=5000) (base:=14436) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page45Checked.down

private theorem page45Good : GoodPage page45Data := by
  have anchor : oddCount 14436 = 3143 := by exact page44Good 63 (by decide)
  exact (page45 anchor)

private def page46Data : ℕ := 0x6a2001ed400350c00f69001a78007b0c00d3a003d7c0069c001eb90034e000f5b401a70007aa800d33003d4000699001e9c8034c000f4c401a58007a3000d2b003d1400693001e8400349400f41001a48007a0200d1f003ce90068e801e7300347400f39401a380079b800d1a003cd80068c001e6900344400f2b001a1a00793800d0b003c8a00684801e4000342000f1e001a100078e800d06003c6e00682001e3000340c00f17401a060078b400cff003c490067f801e240033f000f0f8019ec00784800cf5003c1c00679001e060033c000eff0019d80077d800ceb003be800673801dec80339800ef58019ca0077a200ce5003bce00672801de680338000eea8019bc00773e00cdc003b950066e001dca00336800ee38019b200771000cd9003b840066b801dc000335c00edf0019ac0076f000cd5003b6f0066a001db500334c00ed80019a20076b000cd0003b4600664801d9400332400ec880198a00762c00cc1003afc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page46Checked : PLift (fastPage primes 11 10 15064 720 3257 page46Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page46 (anchor : OMA.PrimePopulation.oddCount 15064 = 3257) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page46Data i)) =
      rowCount (packedEvent page46Data i) := by
  exact fastPage_sound (width:=720) (bound:=5000) (base:=15064) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page46Checked.down

private theorem page46Good : GoodPage page46Data := by
  have anchor : oddCount 15064 = 3257 := by exact page45Good 63 (by decide)
  exact (page46 anchor)

private def page47Data : ℕ := 0x6f380207000379401036401bc200818e00dde0040b6006ef00205a8037780102c801bb600814e00ddb0040a3006ed00205000376001026001baa00811000dd3004081006e900203f0037440101d801ba00080e200dcf004070006e70020360037340101a401b9a0080d000dcc004065006e580203000372801016001b8800807e00dc2004029006df00200e0036ec01003001b7400801400db7003ffd006db801ffe0036cc00ff8c01b64007fc000dae003fbd006d4801fd400368800fe3001b38007ee800d9b003f6d006c9801fa400364c00fd0c01b26007e8000d8f003f36006c2001f8880361000fc2401afa007dc000d73003eaf006b9001f550035ac00fa6401ad6007d2a00d6b003e90006b4801f4600359c00fa0001ac4007cd400d62003e58006b0001f2380357400f8d801ab6007c6200d59003e19006aa001efd00354000f7c801a9e007bca00d4e003de2006a4801ee400352000f71001a90007b8200d46003db3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page47Checked : PLift (fastPage primes 11 10 15784 824 3396 page47Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page47 (anchor : OMA.PrimePopulation.oddCount 15784 = 3396) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page47Data i)) =
      rowCount (packedEvent page47Data i) := by
  exact fastPage_sound (width:=824) (bound:=5000) (base:=15784) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page47Checked.down

private theorem page47Good : GoodPage page47Data := by
  have anchor : oddCount 15784 = 3396 := by exact page46Good 63 (by decide)
  exact (page47 anchor)

private def page48Data : ℕ := 0x73f8021f18039f8010f8001cf80087b200e7b0043d40073d0021e68039e8010f2401cee00877800e740043b1007398021d68039c4010e6c01cdc00872400e6e004391007360021c60039a0010db001cce0086d400e65004364007318021ae003988010d6c01cc20086b000e5f00434f0072f0021a4003970010cf401cb200864200e5600431c00729802184803930010bb801c960085da00e470042db0072380216c803910010b1801c8400857400e3f0042b10071f8021580038f0010a9c01c7800854c00e3b0042930071d8021480038d80109c801c6a0084dc00e34004263007190021260038c401092801c5400844e00e2a0042240071400211000389c01086001c4e00842a00e170041ce0070b0020e18038580106e801c2c00837200e0c00419d007040020ca0038080105cc01c000082d200dfd00415b006fd0020a28037d40104c001bea00825e00df2004122006f88020908037a401040401bd00081d800de80040e6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page48Checked : PLift (fastPage primes 11 10 16608 771 3559 page48Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page48 (anchor : OMA.PrimePopulation.oddCount 16608 = 3559) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page48Data i)) =
      rowCount (packedEvent page48Data i) := by
  exact fastPage_sound (width:=771) (bound:=5000) (base:=16608) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page48Checked.down

private theorem page48Good : GoodPage page48Data := by
  have anchor : oddCount 16608 = 3559 := by exact page47Good 63 (by decide)
  exact (page48 anchor)

private def page49Data : ℕ := 0x7910023b3003c78011d5c01e3a008e9200f1b0047410078d8023a0003c5c011cd801e28008e5000f1100470800788802383803c44011c1801e22008e0a00f100046fe0078700237d003c10011b1401dfe008d5000efe0046a00077e80234c003bec011a4001df2008d0400ef800467e0077b00233a003bd80119cc01de8008cce00eef0046500077480231d803b9c0118b001dca008c4600edc0045f60076d8022f8003b6001179001dae008bb000ed20045c8007690022e2803b480116c401da4008b6000ed00045a8007680022ca803b3401161801d92008ae800ec900456f007640022b5803b0c01158001d7a008a7600ebd0045380075e00229a003ae001148c01d6e008a3c00eb60045120075a002286003ad001142001d5e0089e400ead0044e800753802265003a980112e001d4200894000e990044840074c00223e003a580111d801d260088cc00e9300445c00749002226803a380110d001d040087ea00e820043f3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page49Checked : PLift (fastPage primes 11 10 17379 899 3711 page49Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page49 (anchor : OMA.PrimePopulation.oddCount 17379 = 3711) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page49Data i)) =
      rowCount (packedEvent page49Data i) := by
  exact fastPage_sound (width:=899) (bound:=5000) (base:=17379) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page49Checked.down

private theorem page49Good : GoodPage page49Data := by
  have anchor : oddCount 17379 = 3711 := by exact page48Good 63 (by decide)
  exact (page49 anchor)

private def page50Data : ℕ := 0x7dd802548003ed80129bc01f6c0094d400fb3004a52007d8802522803ebc0128d801f5000943400fa6004a01007d28024ff003e900127e801f480093f000fa30049f7007d10024f9003e800127a801f3200935e00f980049a9007cc0024d4003e5c01268401f2200930400f9000497f007c80024bd003e3c0125d801f1c0092da00f8800495f007c38024ac003e0c01252401f0600928e00f7c004930007bd802494003dd401240001ee20091e000f6f0048e8007b5802469003da001230401ed000918000f670048b4007b2802456003d900122a001ec000912a00f5c00487e007ae00243d003d6c0121c401eb40090de00f5a004864007aa002426003d440120f001e9e00906000f4a00481c007a480240d803d1801204001e8600900000f420047f80079d8023ec003ce4011f4001e6a008f7800f2e0047a1007970023d0003cb4011e7001e5a008f3200f2c004796007958023c7803ca8011e2c01e52008f0000f23004768

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page50Checked : PLift (fastPage primes 11 10 18278 810 3874 page50Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page50 (anchor : OMA.PrimePopulation.oddCount 18278 = 3874) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page50Data i)) =
      rowCount (packedEvent page50Data i) := by
  exact fastPage_sound (width:=810) (bound:=5000) (base:=18278) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page50Checked.down

private theorem page50Good : GoodPage page50Data := by
  have anchor : oddCount 18278 = 3874 := by exact page49Good 63 (by decide)
  exact (page50 anchor)

private def page51Data : ℕ := 0x83400270b00419c013850020cc009c1801064004dff008318026f900417401376c020aa009b7601054004db7008290026d600413801365c0209c009b2a0104b004d80008250026be00411c0135d00208e009ae001047004d6a008218026ac8041000135080207e009a760103e004d3a0081f00269c8040f80134d00207a009a580103b004d280081a8026818040c80133bc0205200999201026004cb30081100265000407c01325c0203c0099280101e004c920080e8026470040600131e00202e0098de01016004c68008078026230040300130ec0201600986c0100a004c3000804002610003fe0012f3401fde00973e00fe7004b83007f38025bf803f78012d5001fb400967800fda004b38007ec802594003f50012c5001fa800962600fd3004b08007e9802582003f4c012c0001f9e0095c600fca004ad5007e4802567003f1c012b1c01f8800957400fc1004aaa007e0802554003f00012a9001f7e00953800fbe004a97

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page51Checked : PLift (fastPage primes 11 10 19088 902 4027 page51Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page51 (anchor : OMA.PrimePopulation.oddCount 19088 = 4027) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page51Data i)) =
      rowCount (packedEvent page51Data i) := by
  exact fastPage_sound (width:=902) (bound:=5000) (base:=19088) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page51Checked.down

private theorem page51Good : GoodPage page51Data := by
  have anchor : oddCount 19088 = 4027 := by exact page50Good 63 (by decide)
  exact (page51 anchor)

private def page52Data : ℕ := 0x8860028c48044280145f80221200a2e801104005158008810028a880440801453c021fe00a290010ff0051470087c8028968043e40144a0021ec00a236010f4005115008768028740043b0014388021d000a1a6010e70050d000871802855004388014290021b000a0fa010d70050790086a8028380043480141a40219c00a0b4010cb005048008658028208043240140c80218a00a046010c50050210085f0027fb8042f0013fc802176009fd8010b6004fce008588027de0042b8013ed40215c009f64010ad004fb0008560027d30042ac013e7c0214e009f20010a7004f89008518027b400428c013d9402142009ebc0109f004f500084c80279780425c013c9002120009e0c0108f004f050084780278080422c013bb402116009dd20108b004ee40083f8027498041fc013a30020f8009cf401077004e6b0083a00272d8041c0013908020de009c720106c004e2d008360027150041b001389c020d4009c4001069004e18

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page52Checked : PLift (fastPage primes 11 10 19990 883 4200 page52Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page52 (anchor : OMA.PrimePopulation.oddCount 19990 = 4200) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page52Data i)) =
      rowCount (packedEvent page52Data i) := by
  exact fastPage_sound (width:=883) (bound:=5000) (base:=19990) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page52Checked.down

private theorem page52Good : GoodPage page52Data := by
  have anchor : oddCount 19990 = 4200 := by exact page51Good 63 (by decide)
  exact (page52 anchor)

private def page53Data : ℕ := 0x8d8802a6f0046bc0153480235a00a992011ac0054c4008d4802a5e8046a00152840234400a9000119f00546a008ce802a3000467401517c0233800a8b20119b005454008cc002a1e80465c0150d80232a00a848011840053cf008c08029db8045fc014ec4022f600a7440117b00539e008bc0029c70045dc014e24022ee00a7100117100536c008b80029b48045b4014d88022d600a6b801169005355008b30029a1004594014cd0022c800a6560116400532a008b180299400458c014c9c022b600a5f0011530052e2008a900296a80452c014b000229200a566011480052b0008a300295400450c014a5c0228200a522011400052860089f00293c0044ec0149b00227400a4d20113100523a008980029190044b00148840225800a43e0112b0052180089580290b8044ac0148540224c00a402011200051ef0088f0028f50044700147640222e00a392011160051c00088a8028de80444c0146e00222600a368011110051a8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page53Checked : PLift (fastPage primes 11 10 20873 853 4364 page53Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page53 (anchor : OMA.PrimePopulation.oddCount 20873 = 4364) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page53Data i)) =
      rowCount (packedEvent page53Data i) := by
  exact fastPage_sound (width:=853) (bound:=5000) (base:=20873) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page53Checked.down

private theorem page53Good : GoodPage page53Data := by
  have anchor : oddCount 20873 = 4364 := by exact page52Good 63 (by decide)
  exact (page53 anchor)

private def page54Data : ℕ := 0x943002cb5004a140165a0024fc00b2800127e00593f0093e802c9e8049b4016398024d400b1ae012660058b600932802c5800498c016288024c400b13e0126200589d00930802c4c004974016210024b600b1040124e00582a00921002bf20048f0015f200247800af8c0123b0057c00091a802bd38048cc015e600245a00aef00122b00577200914802bb20048a0015d740244400ae740121e00572f0090e802b95804848015bd40242400ade8012110056f000907002b73004830015b6c0241200ad800120300569700901802b420047ec0159bc023f600acdc011fa005661008fa802b270047cc015900023e000ac60011ef00562d008f6002b110047a8015864023cc00ac08011e60055ff008f1002af800477c015798023ba00abc0011d80055cc008eb802ae18047500156a4023a600ab30011cc00557d008e4802ab20047180155540238c00aaa2011c4005543008dd802a910046e40154700237000aa1e011b6005505

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page54Checked : PLift (fastPage primes 12 11 21726 1164 4529 page54Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page54 (anchor : OMA.PrimePopulation.oddCount 21726 = 4529) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page54Data i)) =
      rowCount (packedEvent page54Data i) := by
  exact fastPage_sound (width:=1164) (bound:=5000) (base:=21726) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page54Checked.down

private theorem page54Good : GoodPage page54Data := by
  have anchor : oddCount 21726 = 4529 := by exact page53Good 63 (by decide)
  exact (page54 anchor)

private def page55Data : ℕ := 0x9a3002ec3804d140176100268800baf601342005d7000999002e92804cc80174900265c00ba200132d005d0800995002e7c004c940173900264400b9a40131c005cbc0098d802e58004c580172500262600b91001312005c7e00988802e3e004c3c0171c00261c00b8ce0130c005c6200983802e27004c1c0171300260a00b88001302005c220097d002e02804be0016fe4025ea00b7d0012f3005bd700977802ddb004bbc016ed0025da00b744012ed005ba100975802dc9804bac016e40025c200b6b4012dd005b4f0096d002d9f004b64016ccc025b200b664012d7005b2e0096a002d91804b50016c800259800b5f8012c8005ade00962802d69004b10016b440258600b594012bd005ab40095d002d4d804ae4016a580257200b512012b5005a7b00956802d27004ab00169240255600b482012a6005a2a00950002d04804a680167b00252e00b39c012940059c100947802ccc004a3c01665c0250c00b2f001286005972

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page55Checked : PLift (fastPage primes 12 11 22890 1053 4742 page55Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page55 (anchor : OMA.PrimePopulation.oddCount 22890 = 4742) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page55Data i)) =
      rowCount (packedEvent page55Data i) := by
  exact fastPage_sound (width:=1053) (bound:=5000) (base:=22890) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page55Checked.down

private theorem page55Good : GoodPage page55Data := by
  have anchor : oddCount 22890 = 4742 := by exact page54Good 63 (by decide)
  exact (page55 anchor)

private def page56Data : ℕ := 0x9fa003096004fc4018484027e000c238013ed006104009f4003078004f9c0183ac027cc00c1c8013e50060e1009f200306d804f9001835c027be00c17a013dc0060ac009ed803051804f64018268027aa00c110013d0006073009e6803030804f280181580279400c0a8013c900604b009e4003021804f200181080278c00c076013c300601f009de803006004ee80180040277400c000013b5005fe8009d8802fe6804ea8017ed00274e00bf3e013a5005f8a009d2802fc4004e90017dfc0273a00beca01398005f4b009c7802f92804e3c017c880271e00be2c0138d005f12009c6002f87804e2c017c280271600be0e01389005efe009c4002f7b004e0c017b740270600bdb40137e005ec6009bb802f54804dcc017a34026e200bd100136d005e6d009b5802f2e804da0017954026c400bc4c01351005dc3009a8802edc804d340176b40269a00bb580134d005da8009a5002ed0004d1c0176400268c00bb1801346005d89

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page56Checked : PLift (fastPage primes 11 10 23943 933 4934 page56Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page56 (anchor : OMA.PrimePopulation.oddCount 23943 = 4934) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page56Data i)) =
      rowCount (packedEvent page56Data i) := by
  exact fastPage_sound (width:=933) (bound:=5000) (base:=23943) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page56Checked.down

private theorem page56Good : GoodPage page56Data := by
  have anchor : oddCount 23943 = 4934 := by exact page55Good 63 (by decide)
  exact (page56 anchor)

private def page57Data : ℕ := 0xa758033368053ac0199b0029c800cc72014e300663000a6e80330880536c019824029b200cbf8014d90065f800a6c0032f88053440197580299c00cb80014c800659d00a628032c40053000195b40296600ca66014ad00650a00a5500327d80529c0193bc0294c00c9cc014a30064da00a5080326680526c0192d00293200c94a0149100648500a4800324080521c0191800290c00c8ac0147d00642300a3e00320f8051cc018fcc028e400c7e00146d0063d800a360031e78051b0018f18028d800c784014690063b400a338031d700517c018dfc028bc00c6f00145800635700a2b8031aa005148018cc80289e00c64e0144d00631800a25803180005124018bb80288c00c5c2014460062d800a20803160005100018aec0286600c4d40142e00625b00a1480311d00509001887c0283e00c4000141d0061f200a0c0030f00050440187080281600c34e0140900619e00a028030c28050080185e8027fa00c2b2013fb00614a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page57Checked : PLift (fastPage primes 12 11 24876 1345 5108 page57Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page57 (anchor : OMA.PrimePopulation.oddCount 24876 = 5108) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page57Data i)) =
      rowCount (packedEvent page57Data i) := by
  exact fastPage_sound (width:=1345) (bound:=5000) (base:=24876) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page57Checked.down

private theorem page57Good : GoodPage page57Data := by
  have anchor : oddCount 24876 = 5108 := by exact page56Good 63 (by decide)
  exact (page57 anchor)

private def page58Data : ℕ := 0xae200357f00570401abc802b8000d5ca015bf006ae200adf00356f0056e801ab2002b7200d57c015b1006a9a00ad70035458056b801aa2802b5600d50a015a5006a6e00ad200352c80568001a92802b3600d47c01596006a2200ac880350480562801a74802b1000d392015860069bd00ac20034d700560801a69402b0200d32c0157f00698c00abf0034c50055f801a61002af000d2c00156b00692600ab500349000559001a40c02abc00d1ba0155000689f00aa580343f00552c01a1ec02a9400d0d00154900686400aa300342a00551001a13c02a8200d0720153b00681800a9b8034038054d8019fe802a6800cfd8015300067da00a970033ea0054b8019f4c02a4000cf120152000678700a8e8033bd005460019dac02a2e00cec80151400675200a8780339d805424019c4002a1000ce120150700670200a838033808053f4019b30029f600cd92014f50066a800a7880334b8053bc019a34029da00cd08014eb006670

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page58Checked : PLift (fastPage primes 12 11 26221 1169 5355 page58Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page58 (anchor : OMA.PrimePopulation.oddCount 26221 = 5355) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page58Data i)) =
      rowCount (packedEvent page58Data i) := by
  exact fastPage_sound (width:=1169) (bound:=5000) (base:=26221) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page58Checked.down

private theorem page58Good : GoodPage page58Data := by
  have anchor : oddCount 26221 = 5355 := by exact page57Good 63 (by decide)
  exact (page58 anchor)

private def page59Data : ℕ := 0xb5f80381d005af801c0c802d7000e01c016b700700900b5b803801805ad801c00802d6000dfbc016ae006fd600b568037ea805aac01bf3002d3e00df2201698006f6e00b490037a6805a3c01bcf002d1400de5401682006f0100b370037510059b801ba8002cd800dd3401668006e8200b2f00372900596c01b93002cb400dc9201654006e2700b2800370b00593801b81002c9800dbe40164c006de700b258036f300592401b77802c9200dbba01641006db500b200036d800590001b6b402c7e00db540163b006d9200b1b8036be0058d801b5d802c5c00da8c01626006d2000b0c00367000585001b33c02c2600d99001611006cc000b0680365700581001b20002bfe00d8c8015fc006c4c00afe0036258057e801b11002bf400d87c015f8006c3000af70035fb0057a801af7402bca00d794015d9006b8500aec0035bc00575c01add802ba000d6a2015c8006b2000ae400358d00571801ac5402b8c00d628015c6006b09

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page59Checked : PLift (fastPage primes 12 11 27390 1340 5572 page59Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page59 (anchor : OMA.PrimePopulation.oddCount 27390 = 5572) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page59Data i)) =
      rowCount (packedEvent page59Data i) := by
  exact fastPage_sound (width:=1340) (bound:=5000) (base:=27390) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page59Checked.down

private theorem page59Good : GoodPage page59Data := by
  have anchor : oddCount 27390 = 5572 := by exact page58Good 63 (by decide)
  exact (page59 anchor)

private def page60Data : ℕ := 0xc01003b94805ff801dc2002fdc00ed68017e500768900bee003b33005f6401d97c02fa800ec64017cc0075f900be2803aea805f1001d71802f8400eb7e017c10075b500bdf803ad8005ef801d6a402f6800eade017ad00754e00bd5803a9f805ea801d4f402f4200e9f40179b0074ca00bcd003a63805e6001d2d802f1600e8f80178b00747800bc5003a3b005e1c01d1c002f0200e8900175e00739400bae8039c7805d3c01cd5402e9e00e69a0174a00733e00ba480399d005cec01cb7802e7200e5a2017360072c000b96003942005c9401c98802e4200e4780171c00722400b888038fd005c4401c7c402e2000e3d4017040071ab00b7f0038c9805be401c5c802df200e2e2016f700716900b798038ad005bcc01c56002de200e29e016ef00714200b7680389a005bac01c4a002dd600e248016e30070f800b70803878805b6801c35802db400e1a0016d20070af00b67803850805b3401c26002d9400e100016c0007042

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page60Checked : PLift (fastPage primes 12 11 28730 1775 5823 page60Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page60 (anchor : OMA.PrimePopulation.oddCount 28730 = 5823) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page60Data i)) =
      rowCount (packedEvent page60Data i) := by
  exact fastPage_sound (width:=1775) (bound:=5000) (base:=28730) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page60Checked.down

private theorem page60Good : GoodPage page60Data := by
  have anchor : oddCount 28730 = 5823 := by exact page59Good 63 (by decide)
  exact (page60 anchor)

private def page61Data : ℕ := 0xca2003f2d00650c01f9380327200fc4801935007e1200c9a803f038064d401f8080326400fbe601931007df000c96803ee88064a401f6c00324200fb0801917007d4800c8b003e9d00645401f4c00322800fa5a01912007d2000c88003e8900643401f4140321000f9b401905007cc800c7a003e388063c001f194031d400f89c018e8007c3e00c71003e1880638401f090031b800f810018d1007bd600c67003de700633801ef340318c00f754018c1007b8c00c5d803db10062ec01ed680317400f6a2018af007b1800c57803d880062bc01ec340315e00f6100189f007ac000c4b803d4380624001e9740311e00f4aa0188c007a4c00c41003d0900620001e81c030f800f3da018700079a600c2d803c9600616801e4a4030ae00f2320185300790b00c26803c7500611801e2d00308600f1360183d00787800c1d803c380060c801e1240306200f0840182900782000c09803bd180602c01dda80301600eecc01802007731

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page61Checked : PLift (fastPage primes 12 11 30505 1841 6146 page61Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page61 (anchor : OMA.PrimePopulation.oddCount 30505 = 6146) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page61Data i)) =
      rowCount (packedEvent page61Data i) := by
  exact fastPage_sound (width:=1841) (bound:=5000) (base:=30505) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page61Checked.down

private theorem page61Good : GoodPage page61Data := by
  have anchor : oddCount 30505 = 6146 := by exact page60Good 63 (by decide)
  exact (page61 anchor)

private def page62Data : ℕ := 0xd3b00426e8069b80212cc034d601095801a6900849b00d3400424c806964021140034a801086a01a5400843000d27004204006910020f680347e01079201a3f0083c600d1e8041db8068d0020e50034620106f801a3000837200d150041a700687c020c880343601060a01a170082f600d0a00417600684c020b8c034220105a001a0600829b00d010041458067f002097c033d6010404019eb0081fe00ce98040bd8067480205e4033a20102c8019cf00815600ce300408c00671802045403384010202019bf0080f700cdf0040768066f40203880337001018e019a800806800cd300402e80665c0200800332a0100320199200800c00cc680400000663001ffe00331600ffde01989007fd800cba803fb60065ac01fcd4032ca00fe4601964007f2000caf003f8080657401fbe0032b800fde80195b007eea00cad803f7380655801fb30032a000fd6601950007eb100ca6003f4800652401fa040328e00fcd601946007e65

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page62Checked : PLift (fastPage primes 12 11 32346 1667 6468 page62Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page62 (anchor : OMA.PrimePopulation.oddCount 32346 = 6468) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page62Data i)) =
      rowCount (packedEvent page62Data i) := by
  exact fastPage_sound (width:=1667) (bound:=5000) (base:=32346) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page62Checked.down

private theorem page62Good : GoodPage page62Data := by
  have anchor : oddCount 32346 = 6468 := by exact page61Good 63 (by decide)
  exact (page62 anchor)

private def page63Data : ℕ := 0xdc3804582006e14022bf4037020115e001b7f008ae600dbf80456d806de8022ae0036dc01151801b66008a6300daf004519006d740228a8036b801144601b59008a0c00dab0044fd006d540227d80369801138c01b480089b000d9f8044bf006cf40225d8036740112ca01b3600894e00d9a8044a4806ccc0224f80365e01125201b2800891000d9280447f006c740223600363201118001b180088bb00d8a004455006c2c0221c0036120110c801b0500885000d8080441d806bf8022088035fa01104001af60087d200d7a8043e0006bbc021ec0035c2010eca01ad800872e00d6a00438c806b3c021c0c0359a010df401acc0086e800d65004370006b28021b600358c010d9001ac40086c000d61004351006b04021a7403578010d1e01aad00863800d53004309006a840217c003540010bc001a980085c400d488042d1006a440216600351e010b2001a8600854000d4300429f806a080214d0034fc010a1a01a7a0084f8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page63Checked : PLift (fastPage primes 12 11 34013 1575 6774 page63Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page63 (anchor : OMA.PrimePopulation.oddCount 34013 = 6774) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page63Data i)) =
      rowCount (packedEvent page63Data i) := by
  exact fastPage_sound (width:=1575) (bound:=5000) (base:=34013) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page63Checked.down

private theorem page63Good : GoodPage page63Data := by
  have anchor : oddCount 34013 = 6774 := by exact page62Good 63 (by decide)
  exact (page63 anchor)

private def page64Data : ℕ := 0xe8c8049da80744c024e5c039dc0125a601ce90092b500e74004956007398024a88039cc01252e01cdf00926600e6f00492e0073340248300398a0123dc01cc10091d000e5e8048da0072d8024644039600122dc01c9c00910800e4d80487b80722c0242c00390601210001c8100907100e3f0048300071ec024130038f001207e01c7400901e00e388048070071a4023f9c038c0011f7001c5f008fb400e2f0047d8007160023e40038a6011ee201c43008f1300e208047800070f4023b5003874011d7801c2d008e7d00e1280473100708c02396c03834011c2e01c13008df500e098046fa00702402371c0380a011b5601c04008da800e020046ce00700802366003800011b1801bf9008d5900dfc0046aa806f70023300037b401196e01bc6008c5500de1804624006f080231180378401188401bbe008c2b00ddb0045fe806eb0022ef00374601171201ba3008b8800dc88045a5006e44022d000372001167a01b8b008b28

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page64Checked : PLift (fastPage primes 13 12 35588 2225 7047 page64Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page64 (anchor : OMA.PrimePopulation.oddCount 35588 = 7047) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page64Data i)) =
      rowCount (packedEvent page64Data i) := by
  exact fastPage_sound (width:=2225) (bound:=5000) (base:=35588) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page64Checked.down

private theorem page64Good : GoodPage page64Data := by
  have anchor : oddCount 35588 = 7047 := by exact page63Good 63 (by decide)
  exact (page64 anchor)

private def page65Data : ℕ := 0xf2d804d75807964026b8803cb00135b001e52009aba00f24004d4600791c026a0003c8c0134f401e46009a7900f20804d2b0078f80268e403c7c01347001e3e009a3000f1d804d108078e402685403c6801340201e34009a0000f19004cf70078a402670003c4c01336801e1d00997800f0e004cba80785402655803c2601329001e0d00992000f06804c8e80783402646803c1801321001e000098c500efa004c400077c00261b003bd401309201de400982100ef1804c0a80778402602403bb8012fd201dd20097c000ed9804b960076a4025bc803b50012ddc01da80096ec00ed0004b690076440259c803b12012c7801d8300962000ebd804af98075e00257a003aee012bba01d6b00958e00eb3004ab980757c02555803ab2012a5801d4f0094ee00ea6004a7180752802532003a8e01297a01d470094bc00ea3004a5c8075140252c003a8401294001d2c00940f00e95004a04007498024fd403a400127b001d1d0093c6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page65Checked : PLift (fastPage primes 12 11 37813 1846 7449 page65Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page65 (anchor : OMA.PrimePopulation.oddCount 37813 = 7449) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page65Data i)) =
      rowCount (packedEvent page65Data i) := by
  exact fastPage_sound (width:=1846) (bound:=5000) (base:=37813) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page65Checked.down

private theorem page65Good : GoodPage page65Data := by
  have anchor : oddCount 37813 = 7449 := by exact page64Good 63 (by decide)
  exact (page65 anchor)

private def page66Data : ℕ := 0x10170052878080800293500403a01498e0201b00a4b00100a8052490080480292080400a01488e0200500a44200ffb0051f0007fb4028e9c03fda01474601feb00a39d00fef0051a6007f60028cc803fae01464201fcc00a2e500fe4005168007f04028a8803f6c0144c601fa600a20000fd00050e9807e7802872803f0601427401f8200a13100fbc805087007ddc0283e003eee0141e401f7400a0e100fba00506f007db40282cc03ec801411201f5b00a05000fa6805008807cf8027f0803e6a013f1c01f2b009f5c00f87804f5b007c34027a9403e0e013d1001f02009e6600f7c004f1f807bc402787003da6013b1801ed2009d8800f65804eb4007af40273e403d5c01396401ea7009c9100f53804e47807a8c02721003d460138f401ea1009c6d00f4f004e2b807a34026fe003d0c0137c401e82009bca00f40804dd50079fc026ea003cf401372001e74009b7c00f36004da9007998026c7c03cc001360001e5e009af6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page66Checked : PLift (fastPage primes 13 12 39659 2596 7771 page66Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page66 (anchor : OMA.PrimePopulation.oddCount 39659 = 7771) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page66Data i)) =
      rowCount (packedEvent page66Data i) := by
  exact fastPage_sound (width:=2596) (bound:=5000) (base:=39659) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page66Checked.down

private theorem page66Good : GoodPage page66Data := by
  have anchor : oddCount 39659 = 7771 := by exact page65Good 63 (by decide)
  exact (page66 anchor)

private def page67Data : ℕ := 0x111180582080885402bfe404410015f900220700afc1010fc8057bb8087dc02bdb8043de015e74021ec00af23010e800574e80873002ba400438c015cc0021c300ae4c010d98056fe0086c402b7d00434c015b6c021a200ad9f010ce0056be80865c02b5c804324015aae0218000acda010bc0056560085cc02b20c042d80158ac0216a00ac49010b300560b80859002b014042ba0157b60215400aba7010a30055aa00851002ad280428601568c0213f00ab3a0109d0055920084e402ac80042560155c80212900aadc0109400556580846402a9e00420a0154040210300a9f90107c0054d70083d002a684041cc01528e020e600a93b0107000548880837002a3f0041a80151a4020d400a8d1010678054590082d402a0f80415a015030020ad00a808010510053dd808284029eb40412e014ef60208400a714010400053808081cc029ac8040e2014d480206e00a688010270052ee0080e802959404068014a700203200a524

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page67Checked : PLift (fastPage primes 13 12 42255 2866 8238 page67Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page67 (anchor : OMA.PrimePopulation.oddCount 42255 = 8238) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page67Data i)) =
      rowCount (packedEvent page67Data i) := by
  exact fastPage_sound (width:=2866) (bound:=5000) (base:=42255) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page67Checked.down

private theorem page67Good : GoodPage page67Data := by
  have anchor : oddCount 42255 = 8238 := by exact page66Good 63 (by decide)
  exact (page67 anchor)

private def page68Data : ℕ := 0x1225005e3600910002f0b8048720178140242b00bbb201215005dd780906802ed54048100175e80240400bade011ff805d5f808ff002eaa8047e80174fa023ec00ba5b011f2805d16008f8002e84c047a2017398023ca00b9b5011df005cb3808ee802e5200477401728a023a900b8f2011c6805c2d008e3002e14c0470e0170740238300b829011c0805c0d008e0002e054046e6016f7e0237000b7ac011b1005bb5808d7002dd20046b8016e8e0235b00b741011ac805b9b008d5002dc10046a0016dc40234c00b6c3011a3805b56008d0402da5c0467e016d200233a00b66201194805b09008c9002d7bc04638016b9a0231c00b5cc0118c005ad9008c6002d6c40461a016ad80230400b53e0116f805a40008b4002d11c045800167ec022b900b3c2011560059bc808aa802cdb40454a0166a2022a300b3470115080599e8089fc02c9c0044fe0164d80227900b2480113a00591100899002c78c044840161fc0224000b0f5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page68Checked : PLift (fastPage primes 13 12 45121 3115 8739 page68Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page68 (anchor : OMA.PrimePopulation.oddCount 45121 = 8739) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page68Data i)) =
      rowCount (packedEvent page68Data i) := by
  exact fastPage_sound (width:=3115) (bound:=5000) (base:=45121) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page68Checked.down

private theorem page68Good : GoodPage page68Data := by
  have anchor : oddCount 45121 = 8739 := by exact page67Good 63 (by decide)
  exact (page68 anchor)

private def page69Data : ℕ := 0x13420064ac8099f803250404cf20192160267700c9060132b00641a00993803203004c980190000264900c7e2013230063ea0098a8031d2404c46018e600261000c6c1013008063388097e003190004bdc018c20025df00c5b9012ed0062d200975c03165004bac018b24025d400c582012e48062a580971c03150404b8e018a80025c500c534012de80627d0096d803135c04b60018956025a900c47f012cf0062228096740310f004b1201879e0257f00c390012b580618400954c030a2c04aa60185100253c00c2040129d8060fc0094d003073404a5801833c0251700c13601286006084009400030300049f2018124024f900c08a0127200601180934002fe6804998017eea024c900bf6701263805fac8092c402fb700495c017d78024a100be850124e805f3400925c02f91804920017c400248800bdda0123f005ed10091f802f67c048f8017b120245c00bceb0122e005e7480914002f2400489e01790e0244e00bc80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page69Checked : PLift (fastPage primes 13 12 48236 3309 9290 page69Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page69 (anchor : OMA.PrimePopulation.oddCount 48236 = 9290) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page69Data i)) =
      rowCount (packedEvent page69Data i) := by
  exact fastPage_sound (width:=3309) (bound:=5000) (base:=48236) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page69Checked.down

private theorem page69Good : GoodPage page69Data := by
  have anchor : oddCount 48236 = 9290 := by exact page68Good 63 (by decide)
  exact (page69 anchor)

private def page70Data : ℕ := 0x1477006bc700a3b4035e24051c201ae98028e100d74801470006ba200a308035a040517401ac92028b700d62801457006afe80a2800356c00511e01aa980287e00d4ed01438006a5900a198035200050c001a8ca0285800d42d014260069f180a130034f680507201a6d20281a00d2c001404806931809ff403488004fe801a39c027ef00d1a0013f40068b7009f6803447c04f9c01a1b2027cd00d0d4013e2806858009f0c03426004f8601a12c027c200d091013dd006839809ed403416004f40019fb20278e00cf92013c68067c8009e1c033d9c04f00019e820277800cf02013b580675d009da4033a8404eb8019c9e0275c00ce4d013a6806704809cc003358404e58019a700272600cd1201392806684009c7803339004de40197ec026eb00cbc5013738065db809b40032cd004d6e019560026b600ca9901359006541009ab403299404d50019498026a500ca43013478064d1809a240325e004d0e0192c60268500c95a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page70Checked : PLift (fastPage primes 13 12 51545 3637 9860 page70Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page70 (anchor : OMA.PrimePopulation.oddCount 51545 = 9860) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page70Data i)) =
      rowCount (packedEvent page70Data i) := by
  exact fastPage_sound (width:=3637) (bound:=5000) (base:=51545) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page70Checked.down

private theorem page70Good : GoodPage page70Data := by
  have anchor : oddCount 51545 = 9860 := by exact page69Good 63 (by decide)
  exact (page70 anchor)

private def page71Data : ℕ := 0x163b00761880b18003af40058b201d75a02c4a00eb52016248075a080b11803acb40588c01d65802c3a00eadd0161c80756a80b0a403a9e40581201d3a402bf500e971015e680743c80aea0039e400572c01ce4002b8e00e6e4015be80733980add8039930056b201cb9202b5600e5b0015a80072c480acf80394800566e01c9f402b2e00e4c30159000723900ac600391380562a01c86c02b0c00e402015798071b000aba8038c74055c601c5e202add00e2d40156d80716400aae80388880556001c3e002aa800e1c80154e0070bc00aa700385cc0553601c2e202a8e00e12d0154300707b80aa180383d8054e401c0ea02a5900dfed0151d006f9100a8cc037c0c0541c01bc5602a0300dddb01501806ee880a7540373500538201b900029c000dc72014d3806de380a664036d800531c01b6620298400daf8014c0006d7500a5f4036b6c052f001b55a0297300da8e014ae806d0b00a54c0367880523401b12a0290c00d841

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page71Checked : PLift (fastPage primes 14 13 55182 5283 10478 page71Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page71 (anchor : OMA.PrimePopulation.oddCount 55182 = 10478) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page71Data i)) =
      rowCount (packedEvent page71Data i) := by
  exact fastPage_sound (width:=5283) (bound:=5000) (base:=55182) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page71Checked.down

private theorem page71Good : GoodPage page71Data := by
  have anchor : oddCount 55182 = 10478 := by exact page70Good 63 (by decide)
  exact (page71 anchor)

private def page72Data : ℕ := 0x182980816f00c134040b20060760204b60301701016d018090080ae80c0040403ec05ffc0201b402fd700fff2017e6807fd900bef403fcf005f4e01fd9402fa600fec5017cd007f4480be4c03f99805f2401fcc002f6d00fd6e017b1007e9000bd7803f44005e9c01f99202f2600fbe50178f807ddc80bc0403ec1005de001f56c02ee900fa940176e807d2900bb5803e8b005da601f41802eb500f9600174f807c7680b9d403df2c05cd201ef1002e4c00f6d901721807b4e80b8b803d89405c5201ec3002e1e00f5d2016fe807a8480b7c403d30805bc201e8ce02ddd00f45c016ec007a1c00b74003d02005b6801e6c202da700f311016d300798600b68c03cbe005b2c01e56402d7800f200016b80078e600b58c03c61805ac601e30a02d6200f1800169c80785080b4e003c25c05a7001e12602d3700f084016808077a100b3e803bc7c059b601dcce02cc300edf3016618076f280b2f003b6b00595001da9002c8600ec88

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page72Checked : PLift (fastPage primes 14 13 60465 5805 11382 page72Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page72 (anchor : OMA.PrimePopulation.oddCount 60465 = 11382) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page72Data i)) =
      rowCount (packedEvent page72Data i) := by
  exact fastPage_sound (width:=5805) (bound:=5000) (base:=60465) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page72Checked.down

private theorem page72Good : GoodPage page72Data := by
  have anchor : oddCount 60465 = 11382 := by exact page71Good 63 (by decide)
  exact (page72 anchor)

private def page73Data : ℕ := 0x1a75008f0380d3a4047800069b4023b72034ba011d0201a44008df900d1e8046e14068e80236ac03447011a4e01a1d808d0400d0b80466ec068480232d00342401196601a0f808ca680d0240462d80680202311a033e8011808019e3008b8900cf0c045bf406754022cd60338b011599019a5008a1800cd200450800665c0227200332e01138f0198e00898b00cc44044b7c0661c02259c033050112a90198280895400cc00044a24065de022470032d20111870196200889900cb040444700656202218203297011030019428087de80c9bc043c94064c4021d900325f010eb40192400872400c838043380064180219aa03202010c96018e70085b100c704042c6006378021606031b9010af4018c20084f880c58804244806288021100031220107b80188b8083bd80c420041c44061ce020c80030e40106320187000831100c3240416880615402099a0309801045e0184800821a80c220041000060dc0206e80306c010350

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page73Checked : PLift (fastPage primes 14 13 66270 6953 12371 page73Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page73 (anchor : OMA.PrimePopulation.oddCount 66270 = 12371) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page73Data i)) =
      rowCount (packedEvent page73Data i) := by
  exact fastPage_sound (width:=6953) (bound:=5000) (base:=66270) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page73Checked.down

private theorem page73Good : GoodPage page73Data := by
  have anchor : oddCount 66270 = 12371 := by exact page72Good 63 (by decide)
  exact (page73 anchor)

private def page74Data : ℕ := 0x1db500a29800eda00514800766802877603b2901438901d7d00a13200ebac0507c8075aa0282ba03ac30140f301d5680a03b80eaa40501740754e0280a403aa001403601d33009f6400e87004f4d40742c0279f0039e1013ba201cdf009d6200e67c04e8440733a0274080396c0138e401cad009c4000e45804dbc4071f2026c6e038d701356201c4c8099ea80e1f804ccb8070d002658a0385301324801c1e0098e100e0e004c69807056026272038220130fe01c0b80985e80df6404bd5006fa8025e64037a1012e0001bc98096d480ddec04b47006edc0259bc0375d012c7001ba980961000dd0c04af1406e2c02555c03713012a9901b798094f500db4404a44806d8a0251a0036b901288801b438093c680da0c049dc406cba024d440364601260801b0200924280d7ec04912006bd20247cc035bc01230401add80918100d62004876006af60243020357b01217f01abd0090bb00d4f8048000069fa023d02034ee011e2c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page74Checked : PLift (fastPage primes 15 14 73223 10025 13546 page74Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page74 (anchor : OMA.PrimePopulation.oddCount 73223 = 13546) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page74Data i)) =
      rowCount (packedEvent page74Data i) := by
  exact fastPage_sound (width:=10025) (bound:=5000) (base:=73223) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page74Checked.down

private theorem page74Good : GoodPage page74Data := by
  have anchor : oddCount 73223 = 13546 := by exact page73Good 63 (by decide)
  exact (page74 anchor)

private def page75Data : ℕ := 0x209380b3e1810468059dd4081a602cbc8040d10165c80205500b262010224059074080e602c7420407301639f0202f80b19e01012c058af00808002c4e4040340162130200b00b0990100200583240800002c13403fbd015f2001fdc00af7c00fdc40575e407ee002bae803f64015d4001fa200ae4500fd000571d007e4802b7a403f20015bba01f8300ad8d00fbdc056a8007dce02b45a03ed20159a801f4e80ac4400fa300560c407ca002adca03e290155b801f0a80aaa100f82805541407c0c02a9ca03e040154d401ef400aa1300f770054fc007b9c02a74203da80152ca01ecc80a92600f6480548a807b1a02a40003d6201510c01ead80a86780f51805418407a60029fd003d21014f8d01e8080a77180f3f0053b08079be029bea03cc5014d6901e5d80a69280f1c0052e20078d60296d003c5e014b1a01e1b00a51780f0d40528b00785a0293da03c1701495b01e0a80a4a880f03805248c077e20290a403bb20146b9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page75Checked : PLift (fastPage primes 15 14 83248 8851 15210 page75Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page75 (anchor : OMA.PrimePopulation.oddCount 83248 = 15210) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page75Data i)) =
      rowCount (packedEvent page75Data i) := by
  exact fastPage_sound (width:=8851) (bound:=5000) (base:=83248) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page75Checked.down

private theorem page75Good : GoodPage page75Data := by
  have anchor : oddCount 83248 = 15210 := by exact page74Good 63 (by decide)
  exact (page75 anchor)

private def page76Data : ℕ := 0x250c00ceef01282c067650093fa033a90049b1019b7d024af80ccd901254006654809224032fd2048e70196e80246600cb26812308065880090e80328b2048710194400242e00c9d68120ac064a70090540325240480a0191ba023ef00c866811f7406431408f26031e1004752018d450238e00c600011c54062f6408e10031704046bb0189c10233a80c4000119d4061ff808c60030c82045fc018506022f400c24101175806102408b3c03058a0459c0182b1022b900c0e301154406042008a4002ffb80450d017f4d0228280bf900113a405f9dc089c602fcb0044c6017d920225080be670111e805ef640886c02f44004435017a1b0220080bc70010fac05e1a40875e02ee18043a40176b2021ad00ba7e810d6805d3e00869e02e95e043430174790219b00ba1c010cbc05cfd00862c02e690042c80171950214100b7f101090c05b8c40843802dae6041f5016c80020d600b56881064805a96c082bc02d244041570168f8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page76Checked : PLift (fastPage primes 15 14 92099 13851 16679 page76Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page76 (anchor : OMA.PrimePopulation.oddCount 92099 = 16679) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page76Data i)) =
      rowCount (packedEvent page76Data i) := by
  exact fastPage_sound (width:=13851) (bound:=5000) (base:=92099) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page76Checked.down

private theorem page76Good : GoodPage page76Data := by
  have anchor : oddCount 92099 = 16679 := by exact page75Good 63 (by decide)
  exact (page76 anchor)

private def page77Data : ℕ := 0x2b8280f706015bc407b6700ad8203d8d0056bb01ec3202b3100f51e81586c07a1200ab9603ccaa0558601e4c202ab980f2310154c8078b800aa4c03c4e2054d101e08002a4080ef488150b00772880a7ba03b56a053dc01daa7029d680ecbe014e480763200a67a03adba052ee01d4f20294e80e98481492c0744800a408039e72051b601cd52028d980e69881465c0731fc0a2e40396da0514d01ca990288f80e4c401444c0725400a1aa038f4a0509f01c6350284600e2e101410c070f8409ff603840004fa001c021027a600df21013bfc06f19409dec03786c04eb301ba880273480dc5681393806e03809c30036da404df001b5df026e680da7c8135ec06cc8009a9003637c04d3401b1490268b00d84c81339c06bdc80993a035b3a04c7801acf10262480d5e4012fe806a7d40975803504404b7701a6d0025b380d328812c78069200095f20346ec04ad401a2b10254580d0710129b40680f0094c2033fd804a43019f15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page77Checked : PLift (fastPage primes 16 15 105950 20526 18968 page77Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page77 (anchor : OMA.PrimePopulation.oddCount 105950 = 18968) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page77Data i)) =
      rowCount (packedEvent page77Data i) := by
  exact fastPage_sound (width:=20526) (bound:=5000) (base:=105950) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page77Checked.down

private theorem page77Good : GoodPage page77Data := by
  have anchor : oddCount 105950 = 18968 := by exact page76Good 63 (by decide)
  exact (page77 anchor)

private def page78Data : ℕ := 0x33bc012ad4019dac0955240ce1604a640066b10250f90335281285d019940093b480cbfe04995a065a3024a88032a78124328193f80919080c95c0488420645302420003200811ff0818eac08f7080c6ba04774a0630b02398803159011bb681897808d55c0c4ba046aa40623b02349c0310001199c8186e408c4800c2c8045e1206117022cf20305b81156e8181ac08a3200c030044d6a05fba0224a202fb2011148817cc00884b40be2804410005ee4021f5c02f60810f388179c80871880bc9804370e05e1a021a5502edf810c2401769c085e300bae8042c7a05d2802143202e678109148171ec0840800b852041c3205bd6020c1202dbc81050b816dd80828340b67404114e05b2302080802d860103c5016b380818140b5420409fa05a7f02040202d1301010081675c0800000b31803fc020593c01fc0202c7600fd0281625807e0200b08c03ec1a0583601f58402c0000fa09015ea007c8640aeb403e0400570901ee29

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page78Checked : PLift (fastPage primes 16 15 126476 26524 22277 page78Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page78 (anchor : OMA.PrimePopulation.oddCount 126476 = 22277) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page78Data i)) =
      rowCount (packedEvent page78Data i) := by
  exact fastPage_sound (width:=26524) (bound:=5000) (base:=126476) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page78Checked.down

private theorem page78Good : GoodPage page78Data := by
  have anchor : oddCount 126476 = 22277 := by exact page77Good 63 (by decide)
  exact (page78 anchor)

private def page79Data : ℕ := 0x3e72016ef681f1dc0b6e200f83a05b24a07bba02d6c203db1016a3081ec200b48000f570059f4207a5b02cd4203cfa01657281e6540b22200f270058c5a078db02c3d203c390160bc81e1b00b04b40f048057e40077ca02bcc903bb3815d3901dc440ae0740ed78056b900765502b37503afc01589101d6580abb440ea72055900074d902aa3103a410153f101d0880a96540e7860546900736702a0fd03986814f5901cac00a71a40e4a80534400723f0299a9038fc814bec81c69c0a56480e29005269a070e70291080384881476281c0d00a32080dfae05148206f81028800037920142e081bb340a0ea80dd9005070406e7102814503707813f8401b6ec09f3340dab604f52406cfe02785903655813b1001b14009cfa40d7f004e36406b96026f7d0359a0136a401ac6c09b2880d5b604d62a06a7c0268e20351401335881a7240992000d2de04c4a20691902602203461812efa81a1b4096f200d02a04b33a067c4025772

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page79Checked : PLift (fastPage primes 17 16 153000 34885 26488 page79Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page79 (anchor : OMA.PrimePopulation.oddCount 153000 = 26488) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page79Data i)) =
      rowCount (packedEvent page79Data i) := by
  exact fastPage_sound (width:=34885) (bound:=5000) (base:=153000) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page79Checked.down

private theorem page79Good : GoodPage page79Data := by
  have anchor : oddCount 153000 = 26488 := by exact page78Good 63 (by decide)
  exact (page79 anchor)

private def page80Data : ℕ := 0x4a4681bba10250b00dd2841279806e4000935f036f610497901b661024abc0dab4c1252806d44a09235036788048ed01b2768245a80d8948121f406bf7209092035d200481301ad44823f140d5fc811ed206aaba08f060352c80474b01a81a8238b40d368811b7c06962208d560348800467501a2f88232200d0d881184e0681aa08bca033e48045b1819dde822be40ce4c811534066d5208a36033420044e68198cc8225940cbc481121406591a088a1032a080441d0193c2821f840c940810ef00645020871203200004356818ec08219100c6c0810bda06310a08590031608042968189c68213ec0c48e81099606222408475030e990420a018610020ec00c26a410698060e64082f40304bd041490181240208b40bff541037e05fac40815d02faf10407a017c400202500bd8441007a05e74407fdf02f13503fbe01776401fd140bb6200fe3205d8ba07eb902e9f203f2e0173c481f7f80b94800fb3805c57207d4402e052

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page80Checked : PLift (fastPage primes 17 16 187885 39253 31972 page80Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page80 (anchor : OMA.PrimePopulation.oddCount 187885 = 31972) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page80Data i)) =
      rowCount (packedEvent page80Data i) := by
  exact fastPage_sound (width:=39253) (bound:=5000) (base:=187885) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page80Checked.down

private theorem page80Good : GoodPage page80Data := by
  have anchor : oddCount 187885 = 31972 := by exact page79Good 63 (by decide)
  exact (page80 anchor)

private def page81Data : ℕ := 0x578602127082ba6810880015c56083e420adc2041c42056ae020cb282b37c105a20158f408275a0ac0c0410d2055ce8206fc82acb8102c80155840810920aa59040572054f102014e82a5c40fff201521207f9ea0a89403fa220541381fba8829ee40fd20014e8607e3620a6cc03eee20533481f60a8297d40fa52014b2007ccfa0a52203e3b20525c01f0748291400f7880147c807b6b20a36f03d8920518401eae6828aa80f4c201446c07a08a0a1c303cd82050ac81e5608283c40f2000140f6078a820a01103c28204fd481dfe2827cf40ef42013d9a07749a09e5d03b79204ef801da6c82766c0ec88013a64075ed209cc303acb204e2c81d4fe826fc00e9d201370007492a09b2203a1e204d5581cf988268f00e7200133b40733a20996a03972204c7d81ca3a8262300e47201304a071e3a097c4038c7204ba681c4e4825b900e1c8012d120708f2096290381d204aee81bff90257000dfcb412ab606f910094f70379e5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page81Checked : PLift (fastPage primes 17 16 227138 44447 38029 page81Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page81 (anchor : OMA.PrimePopulation.oddCount 227138 = 38029) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page81Data i)) =
      rowCount (packedEvent page81Data i) := by
  exact fastPage_sound (width:=44447) (bound:=5000) (base:=227138) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page81Checked.down

private theorem page81Good : GoodPage page81Data := by
  have anchor : oddCount 227138 = 38029 := by exact page80Good 63 (by decide)
  exact (page81 anchor)

private def page82Data : ℕ := 0x65ef827290832da4138800195fc09bdc20ca8d04dbc206508826c528326601356201924009a4da0c8a604cf520641b82661c831f2013248018eb4098c120c6e304c2f206337025fee8317f012f32018b0e09736a0c51904b6a20624b0259c883106812c2001874a095ae20c32f04aa62061600253aa8309101291201839809427a0c15c049e3206070024d948301b412608017ff0092a320bf8504921205f8982478682fa8012302017c4e09120a0bdb004860205e9e82418082f34c120000178d008fa020bbe3047a0205db6823b8282ebf011d0201751008e21a0ba0e046e1205ccf82358c82e4b411a0801716c08ca520b84404623205beb822f9e82dd6c11712016dc808b2aa0b67104566205b018229b882d65811420016a40089b220b4b0044aa205a268223da82cf30111320166c20883ba0b2ec043ef205943821e0482c85010e48016350086c720b1330433520586102183682c14010b62015fca08554a0af780427c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page82Checked : PLift (fastPage primes 17 16 271585 49216 44812 page82Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page82 (anchor : OMA.PrimePopulation.oddCount 271585 = 44812) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page82Data i)) =
      rowCount (packedEvent page82Data i) := by
  exact fastPage_sound (width:=49216) (bound:=5000) (base:=271585) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page82Checked.down

private theorem page82Good : GoodPage page82Data := by
  have anchor : oddCount 271585 = 44812 := by exact page81Good 63 (by decide)
  exact (page82 anchor)

private def page83Data : ℕ := 0x756402dab083a93016c8001d3aa0b5d420e96105ab420747282d3f283a1b41692201cfd60b425a0e76f059dd20737402cd3c8399a4165c801cbd20b27920e56c0590720727782c68e8391b81627201c7e40b0cea0e3700583220717482bfe88389a815f2001c3ee0af2620e17d0575e20708202b94a83822415bd201c0160ad7fa0df880568b206f8402b2b4837a201588801bc060abdb20dd82055b9206e8402ac268372401554201b83a0aa38a0db9d054e8206d9182a5a0836a801520001b4540a89820d9b005418206c98829f228362d014ec201b0760a6f9a0d7c105349206ba48298ac835b0814b8801ac920a55d20d5d10527b206aaa82923e8353781485201a8bc0a3c2a0d3e3051ae2069b8028bd8834bf01452001a4fa0a22a20d200050e22068c602857a834424141f201a1280a093a0d01a050172067d1827f24833cb013ec8019d6009eff20ce3d04f4d2066e18278d683352013ba201999c09d6ca0cc5104e842

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page83Checked : PLift (fastPage primes 17 16 320801 53312 52191 page83Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page83 (anchor : OMA.PrimePopulation.oddCount 320801 = 52191) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page83Data i)) =
      rowCount (packedEvent page83Data i) := by
  exact fastPage_sound (width:=53312) (bound:=5000) (base:=320801) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page83Checked.down

private theorem page83Good : GoodPage page83Data := by
  have anchor : oddCount 320801 = 52191 := by exact page82Good 63 (by decide)
  exact (page83 anchor)

private def page84Data : ℕ := 0x85f0834ad0842d4c1a48002158a0d1cc210a42068ac2084d88343928424b41a0e20211600cffda10829067c52083cf833c5c841c6019d48020d3a0ce31210611066df2082c283352e84141c199b20209060cc66a103fc065fa2081c1832e08840bdc196200204d60ca9e2101ef065162080b30326ea8403681929202009e0c8d7a0ffc606433207f9b031fd483faf818f0801fc680c71320fdb506351207e998318c683f2a818b8201f8440c550a0fbaf06270207d8f8311c083ea841880001f44e0c39020f99506190207c8b830ac283e23c1848201f0120c1d1a0f782060b1207b7e0303cc83da001810801ebee0c01520f57505fd3207a7802fcde83d1c417d9201e7d60be5aa0f36805ef620797282f5f883c9b017a2001e3d00bca220f16905e1a20787282ef1a83c188176b201dfbe0baeba0ef5405d3f20776c02e84483b93c1734801db8e0b93720ed4c05c6520766a02e17683b12416fe201d7960b784a0eb4b05b8c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page84Checked : PLift (fastPage primes 17 16 374113 57408 60104 page84Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page84 (anchor : OMA.PrimePopulation.oddCount 374113 = 60104) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page84Data i)) =
      rowCount (packedEvent page84Data i) := by
  exact fastPage_sound (width:=57408) (bound:=5000) (base:=374113) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page84Checked.down

private theorem page84Good : GoodPage page84Data := by
  have anchor : oddCount 374113 = 60104 := by exact page83Good 63 (by decide)
  exact (page84 anchor)

private def page85Data : ℕ := 0x975c03c2f084b8a41e080025b3a0efc4212d0f077a420964483bb3284b0141dca20256de0edd5a12ae7076ad20952683b37c84a6f81d8c80252620ebe92128a6075b720940903abce849df81d4f2024de20e9fea1266d074c22092f183a42884955c1d1200249900e81621243b073ce2091d9839c8a848cc81cd5202453c0e62fa1220c072db2090c08394f48483e81c9880240e40e44b211fdf071e9208faa838d66847b301c5c2023c860e268a11db9070f8208e8f8385e084723c1c2000238080e088211b7707008208d74837e628469881be420233d20dea9a1196206f19208c630376ec8460b81ba88022f3c0dccd21171d06e2b208b4b036f7e8458641b6d2022b160daf2a1150006d3e208a3a836818844fa01b3200226cc0d91a2112d806c522089260360ba8447201af720222880d743a110b406b67208812035964843e801abc8021e180d56f210e8f06a7d2087068352168435f81a8220219de0d39ca10c62069942

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page85Checked : PLift (fastPage primes 17 16 431521 61504 68577 page85Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page85 (anchor : OMA.PrimePopulation.oddCount 431521 = 68577) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page85Data i)) =
      rowCount (packedEvent page85Data i) := by
  exact fastPage_sound (width:=61504) (bound:=5000) (base:=431521) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page85Checked.down

private theorem page85Good : GoodPage page85Data := by
  have anchor : oddCount 431521 = 68577 := by exact page84Good 63 (by decide)
  exact (page85 anchor)

private def page86Data : ℕ := 0xa9df844310854cb82208002a53410fbc2151f10879c20a8b0843ad28542fc21c6202a03c10dada14f880869520a77904329c85397021848029b9210ba1214d2e0858f20a645042a6e852fac214320296c410996a14aca0848a20a51d8422488526982102002920c1078e2148730838620a3ef841a2a851d1420c12028d6810587a1461a0828320a2c28412148513d4208080288aa103832143cf0818120a1a1040a06850ab42040202843a10180a141890808020a07e8402008501a020000027fae0ff80213f4807f80209f5983fa0284f8601fc02027b220fd81a13d0107e81209e3683f20c84ef3c1f8080276a00fb85213abc07d83209d1483ea1e84e6401f4120272040f98aa1386c07c86209bea83e23884dd201f020026d660f79221361d07b8a209ac983da5a84d3e81ec320268b80f59ba133d207a8f20999c83d28484ca841e84802642c0f3a721317f0799520987583cab684c19c1e462025fa60f1b4a12f440789c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page86Checked : PLift (fastPage primes 18 17 493025 65600 77496 page86Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page86 (anchor : OMA.PrimePopulation.oddCount 493025 = 77496) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page86Data i)) =
      rowCount (packedEvent page86Data i) := by
  exact fastPage_sound (width:=65600) (bound:=5000) (base:=493025) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page86Checked.down

private theorem page86Good : GoodPage page86Data := by
  have anchor : oddCount 493025 = 77496 := by exact page85Good 63 (by decide)
  exact (page86 anchor)

private def page87Data : ℕ := 0xbd4f04cb3085e7fc2648002f2ce131b42178d10989420bc1304c27285ddf42602202edba12f85a176430977d20bad304b9bc85d40425bc802e8de12d592173e50966720b9a084b10e85ca882577202e40a12b2ea1716c0955220b86904a86885c0dc2532002df2a12906216ef70943e20b729049fca85b6b424ed202da36126dfa16c800932b20b5f784973485ad7424a8802d57e124bb216a220921920b4c6048ea685a3cc2464202d0a412298a167b80910820b38d8486208599d82420002cbb81207821653508ff820b248847da2858fcc23dc202c6b211e59a162c608ee920b11404752c85862c2398802c1ec11c3d21604a08ddb20afd4046cbe857c402355202bcd011a22a15dd608cce20ae9e0464588572602312002b8081180a215b6e08bc220ad6b845bfa85690c22cf202b35a115f3a1591c08ab720ac410453a4855f94228c802ae94113df2156ab089ad20ab09844b568555e8224a202a9ea111cca15457088a42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page87Checked : PLift (fastPage primes 18 17 558625 69696 86975 page87Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page87 (anchor : OMA.PrimePopulation.oddCount 558625 = 86975) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page87Data i)) =
      rowCount (packedEvent page87Data i) := by
  exact fastPage_sound (width:=69696) (bound:=5000) (base:=558625) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page87Checked.down

private theorem page87Good : GoodPage page87Data := by
  have anchor : oddCount 558625 = 86975 := by exact page86Good 63 (by decide)
  exact (page87 anchor)

private def page88Data : ℕ := 0xd1c7055b50868bc02ac80034494155ac21a1960aa8c20d0708552128680d02a7e2033f261535da19eef0a96520cf238548dc8676902a348033a0815111219c590a83f20cdd3053fae866c0429eb20334c614ec6a199ba0a71a20cc870536888661c829a20032f9214c7e2197210a5f620cb43052d6a86575029592032a6814a37a194880a4d320c9f9052454864d5029108032566147f321920d0a3b120c8af851b468642ec28c8203203c145b0a18f7b0a29020c76d05124086390028800031b3814370218cf40a17020c624850942862e9c2838203160214131a18a630a05120c4e205004c86247c27f0803110213ef52187e409f3320c39e04f75e861a5c27a92030bfc13cbaa1855509e1620c25f04ee788610942762003070a13a822182d809cfa20c11a04e59a860638271b20301de1384ba1805409bdf20bfde84dcc485fc9026d4802fcec13617217dd509ac520be9804d3f685f23c268e202f7da133e4a17b4f099ac2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page88Checked : PLift (fastPage primes 18 17 628321 73792 96926 page88Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page88 (anchor : OMA.PrimePopulation.oddCount 628321 = 96926) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page88Data i)) =
      rowCount (packedEvent page88Data i) := by
  exact fastPage_sound (width:=73792) (bound:=5000) (base:=628321) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page88Checked.down

private theorem page88Good : GoodPage page88Data := by
  have anchor : oddCount 628321 = 96926 := by exact page87Good 63 (by decide)
  exact (page88 anchor)

private def page89Data : ℕ := 0xe73385f3708736d42f8800399e617ba421cc480bd8420e5cf05e9b2872bac2f3a203946a17935a1c99b0bc4d20e47585dffc8720e82eec8038f0e176c921c6de0bb1720e32185d64e8716442e9f20389e21745ea1c43a0b9e220e1ca05cca8870bbc2e520038480171f621c1940b8ae20e07585c30a8700c82e052037f1616f8fa1becd0b77b20df0d85b97486f5dc2db8803799e16d2b21bc1b0b64920ddb805afe686ead82d6c203741a16ac8a1b96a0b51820dc5e05a66086e01c2d200036ea61686821b6b40b3e820db00859ce286d5842cd4203698216609a1b40e0b2b920d9b085936c86cad02c888036422163ad21b15b0b18b20d8580589fe86c0242c3d2035ec016152a1aeb00b05e20d70685809886b59c2bf2003597815efa21ac130af3220d5af85773a86aaac2ba7203541215ca3a1a9560ae0720d452056de486a0082b5c8034ec215a4f21a6c20acdd20d3180564968695fc2b1220349a8157fca1a42b0abb42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page89Checked : PLift (fastPage primes 18 17 702113 77888 107406 page89Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page89 (anchor : OMA.PrimePopulation.oddCount 702113 = 107406) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page89Data i)) =
      rowCount (packedEvent page89Data i) := by
  exact fastPage_sound (width:=77888) (bound:=5000) (base:=702113) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page89Checked.down

private theorem page89Good : GoodPage page89Data := by
  have anchor : oddCount 702113 = 107406 := by exact page88Good 63 (by decide)
  exact (page89 anchor)

private def page90Data : ℕ := 0xfd7c06939087e9343488003f33c1a39c21f8e40d17c20fc1586895287de0c3436203ed901a10da1f6110d03520fab4867f1c87d2a033e4803e7d219e8121f32e0ceef20f93d8674ee87c70c3393203e23219bf6a1f05c0cdaa20f7dc066ac887bc143342003dc8e1996e21ed880cc6620f66d8660aa87b0a832f1203d6c6196e7a1eab40cb2320f4fd86569487a53c32a0803d14e1946321e7ea0c9e120f399064c868799ec3250203cb96191e0a1e5130c8a020f234064280878f003200003c63018f6021e25f0c76020f0d20638828783d031b0203c05c18ce1a1df830c62120ef68062e8c8778603160803bad218a6521dcbe0c4e320ee0706249e876d943111203b56a187eaa1d9f50c3a620ec9b861ab887623030c2003afbc1857221d7270c26a20eb460610da8757343073203aa5c182fba1d47b0c12f20e9e8860704874ca03024803a4ec1808721d1c90bff520e88885fd368741c42fd62039f6c17e14a1cf0a0bebc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page90Checked : PLift (fastPage primes 18 17 780001 81984 118375 page90Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page90 (anchor : OMA.PrimePopulation.oddCount 780001 = 118375) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page90Data i)) =
      rowCount (packedEvent page90Data i) := by
  exact fastPage_sound (width:=81984) (bound:=5000) (base:=780001) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page90Checked.down

private theorem page90Good : GoodPage page90Data := by
  have anchor : oddCount 780001 = 118375 := by exact page89Good 63 (by decide)
  exact (page90 anchor)

private def page91Data : ℕ := 0x114e3073bb088a43439c800450981cd942227860e6742113608730f288983c39722044a941cae5a2248c0e51d2111e507263c888c40391c80444bc1c8392221970e3c7211065871b8e88804838c72043eaa1c58ea21e940e272210eea0710e8887450387200438a81c2e6221b960e11e210d6887064a886864381d20432e01c03fa218b50dfcb210bfd86fbb4885ce837c88042cf21bd9b2215ae0de79210a7906f126885114377420427101baf8a212d20dd2821090886e6a0884554372000421381b858220fe80dbd821078f86dc228839a036cc2041b521b5b9a20ce60da8921061e86d1ac882e043678804158c1b31d220a090d93b2104a606c73e88224c36252040fb41b082a207210d7ee21033206bcd88816a035d200409fe1adea2204560d6a22101d206b27a880bc8357f204045e1ab53a2016b0d55721005386a82487ffcc352c803fe861a8bf21fe8a0d40d20fee9069dd687f46034da203f8d81a62ca1fbb40d2c42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page91Checked : PLift (fastPage primes 18 17 861985 86080 129784 page91Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page91 (anchor : OMA.PrimePopulation.oddCount 861985 = 129784) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page91Data i)) =
      rowCount (packedEvent page91Data i) := by
  exact fastPage_sound (width:=86080) (bound:=5000) (base:=861985) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page91Checked.down

private theorem page91Good : GoodPage page91Data := by
  have anchor : oddCount 861985 = 129784 := by exact page90Good 63 (by decide)
  exact (page91 anchor)

private def page92Data : ℕ := 0x12d2e87ebd08966703f48004b1b61f98c22580f0fc6c212ba907e092895a003eee204ab741f6bda254e90fb05212a1487d55c894db43e94804a55c1f3f12251ec0f99f21289187ca2e89418c3e3b2049f4c1f126a24ee50f83a21270b07bf088935343de200499141ee5e224bcf0f6d621258387b3ea8929143d8920492e81eb97a248b60f5732123f687a8d4891c883d308048cb01e8d322459e0f411212267879dc689102c3cd8204867e1e610a2427f0f2b02120e00792c08903e03c8000480681e350223f6e0f150211f5b0787c288f7e83c282047a921e091a23c890eff1211de6877ccc88ec243bd080474a41ddd52239930ee93211c650771de88e0683b792046ea61db1aa236870ed36211ae38766f888d3fc3b22004688c1d86222338d0ebda211964875c1a88c7fc3acb20462701d5aba2307e0ea7f2117e407514488bbf43a748045c7a1d2f7222d760e92521165607467688afc03a1e204566e1d044a22a880e7cc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page92Checked : PLift (fastPage primes 18 17 948065 90176 141766 page92Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page92 (anchor : OMA.PrimePopulation.oddCount 948065 = 141766) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page92Data i)) =
      rowCount (packedEvent page92Data i) := by
  exact fastPage_sound (width:=90176) (bound:=5000) (base:=948065) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page92Checked.down

private theorem page92Good : GoodPage page92Data := by
  have anchor : oddCount 948065 = 141766 := by exact page91Good 63 (by decide)
  exact (page92 anchor)

private def page93Data : ℕ := 0x1466a08a3f08a30004508005166622784228a54113642144bd8898328a230044aa2050fe022495a28723111ed21432d888c7c8a1644444c8050986221a92283f5110772141960880ce8a094443ef205030621ebea280bd10f02213fff88752889fcd44392004fcf421bd6227da110d8e213e6888698a89eff44335204f67a218efa27a7e10c1b213cdb085df489e3b042d8804f0342160b22775110aa9213b4708526689d728427c204e9e621328a2742d109382139b20846e089ca604220004e3be21048227111107c8213822083b6289bdb041c4204dd3a20d69a26ddf1065921368b082fec89b1104168804d6f220a8d226ab4104eb2134f288247e89a480410d204d0b2207b2a267871037e2133628819188997f840b2004ca7e204da22646e102122131d6080dba898b884057204c43020203a2614f100a7213040880264897ee03ffc804be021ff2f225e380ff3d212eb887f7168972883fa2204b7be1fc5ca25b210fdd42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page93Checked : PLift (fastPage primes 18 17 1038241 94272 154205 page93Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page93 (anchor : OMA.PrimePopulation.oddCount 1038241 = 154205) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page93Data i)) =
      rowCount (packedEvent page93Data i) := by
  exact fastPage_sound (width:=94272) (bound:=5000) (base:=1038241) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page93Checked.down

private theorem page93Good : GoodPage page93Data := by
  have anchor : oddCount 1038241 = 154205 := by exact page92Good 63 (by decide)
  exact (page93 anchor)

private def page94Data : ℕ := 0x160858964108b00bc4b080057eb02577c22be7f12b5c215ed40957d28af3604aa620577f22546da2bb1b129d5215d2d094b9c8ae6044a4480571642516122b7e61284f215b8a093f6e8ad8fc49e32056ae024e56a2b492126ca2159dc0933488acbac4982005644a24b4e22b14b1254621584189272a8abe7049212055db624847a2ae0f123c3215696091b148ab17448c080557042454322aab1122412154f2090f068aa43c4860205509424240a2a776120c021534d0903008a9724480000549dc23f4022a42011f402151a808f7028a89fc47a0205438223c41a2a0f011dc121501108eb0c8a7d4447408053cf023945229db811c43214e6c88df1e8a705446e120536a02364aa29a8411ac6214cdc88d3388a63c04682005302a233522297561194a214b4488c75a8a56bc462320529b82305ba29410117cf2149a008bb848a49c045c4805235622d672290eb1165521481008afb68a3d5845662051cf622a74a28da2114dc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page94Checked : PLift (fastPage primes 18 17 1132513 98368 167124 page94Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page94 (anchor : OMA.PrimePopulation.oddCount 1132513 = 167124) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page94Data i)) =
      rowCount (packedEvent page94Data i) := by
  exact fastPage_sound (width:=98368) (bound:=5000) (base:=1132513) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page94Checked.down

private theorem page94Good : GoodPage page94Data := by
  have anchor : oddCount 1132513 = 167124 := by exact page93Good 63 (by decide)
  exact (page94 anchor)

private def page95Data : ℕ := 0x17bb00a2c308bd9d45148005eb522897422f4c5144542179ee0a1f728bcc0c50e2205e44628645a2f141142bd21782d0a12bc8bbe2c507c805dd702831922edcc141272176760a060e8bb06c5017205d67627feea2ea6e13f922174c509f9688ba28c4fb2005cf9a27cc622e6fb13dfe21731309ecca8b95444f4d205c8f02799fa2e39a13c6b21716189e0348b87b44ee8805c2282767b22e02d13ad9216fa389d3a68b79bc4e84205bb1827358a2dcae13948216def09c7208b6bf44e20005b4502703822d951137b8216c3b09baa28b5e784dbc205ad8a26d19a2d5f713629216a8e09ae2c8b51384d58805a700269fd22d2971349b2168e209a1be8b435c4cf5205a008266e2a2cf3c1330e21672f8995588b360c4c920059968263ca22cbdb1318221657e0988fa8b28904c2f2059298260b3a2c88012ff72163d4097ca48b1b244bcc8058bf225d9f22c52712e6d2162288970568b0e0c4b6a205856225a8ca2c1e512ce42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page95Checked : PLift (fastPage primes 18 17 1230881 102464 180491 page95Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page95 (anchor : OMA.PrimePopulation.oddCount 1230881 = 180491) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page95Data i)) =
      rowCount (packedEvent page95Data i) := by
  exact fastPage_sound (width:=102464) (bound:=5000) (base:=1230881) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page95Checked.down

private theorem page95Good : GoodPage page95Data := by
  have anchor : oddCount 1230881 = 180491 := by exact page94Good 63 (by decide)
  exact (page95 anchor)

private def page96Data : ℕ := 0x197ba0afc508cba5857c80065b742bd6c232cda15e4c2195ff8aef128cac4c575e20654642ba1da3295d15ca521943a0ae1dc8c9e5456f48064d562b6d12325ce15aff2192788ad4ae8c9018568b206461c2b386a322241595a2190ab0ac7888c81c856220063f0c2b03e231ea1157b6218edd8aba6a8c731455b920637ca2acf7a31af615613218d060aad548c64d0555080630a02a9b323177215471218b4b8aa0468c56dc54e820629aa2a670a313fa152d021898e0a93408c48f0548000622b02a330231078151302187c50a86428c3aa854182061bb229ff1a30cfa14f9121860e8a794c8c2cf453b0806149e29cb523097d14df32184560a6c5e8c1f2453492060de42997aa3061a14c562182a70a5f788c117452e200606fa296422302a014aba2180dd8a529a8c0358527b205fffc2930ba2ff1e1491f217f1d8a45c48bf5645214805f8f228fd722fb9414785217d5f8a38f68be78c51ae205f1f428ca4a2f831145ec2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page96Checked : PLift (fastPage primes 18 17 1333345 106560 194400 page96Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page96 (anchor : OMA.PrimePopulation.oddCount 1333345 = 194400) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page96Data i)) =
      rowCount (packedEvent page96Data i) := by
  exact fastPage_sound (width:=106560) (bound:=5000) (base:=1333345) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page96Checked.down

private theorem page96Good : GoodPage page96Data := by
  have anchor : oddCount 1333345 = 194400 := by exact page95Good 63 (by decide)
  exact (page96 anchor)

private def page97Data : ℕ := 0x1b49e0bd4708da1c05e88006cf1c2f36423669c1794421b2cd8bc6b28d92d45e1a206c7902eff5a362df1778d21b0f18bb8fc8d83bc5dac806c0022ec89235f2a175d721af1d0bab4e8d75505d3f206b8ce2e91ea35b851742221ad518b9da88d66c05cd2006b19c2e5b62357ee1726e21ab820b900a8d58885c65206aa602e24fa3544e170bb21a9b40b82748d4a345bf8806a3362deeb2350b116f0921a7e70b74e68d3b805b8c2069be42db88a34d0916d5821a6130b67608d2d1c5b2000694a42d82823496116ba821a4408b59e28d1e645ab42068d6e2d4c9a345ca169f921a26d0b4c6c8d0fbc5a48806862e2d16d2342341684b21a0a18b3efe8d019859dd2067f1a2ce12a33eac1669e219edb0b31988cf37c597200677e62caba233b11164f2219d190b243a8ce4f8590720670bc2c763a3378116347219b4a0b16e48cd6b0589c806699a2c40f2333e71619d2199838b09968cc898583220662842c0bca3305e15ff42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page97Checked : PLift (fastPage primes 18 17 1439905 110656 208756 page97Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page97 (anchor : OMA.PrimePopulation.oddCount 1439905 = 208756) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page97Data i)) =
      rowCount (packedEvent page97Data i) := by
  exact fastPage_sound (width:=110656) (bound:=5000) (base:=1439905) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page97Checked.down

private theorem page97Good : GoodPage page97Data := by
  have anchor : oddCount 1439905 = 208756 := by exact page96Good 63 (by decide)
  exact (page97 anchor)

private def page98Data : ℕ := 0x1d2b00cb4908e91bc658800746f032b5c23a2841953c21d0ca8ca6528e829c65162073f50327cda39eb21937521cee00c981c8e739064a480737dc32441239b07191af21cd060c89ee8e646c64332073060320b6a3973918fea21cb218c7bc88e557063c200728c431d2e23937918e2621c93c0c6daa8e462c63512072144319a7a38fb118c6321c75f0c5f948e377c62e080719c831623238bec18aa121c57f0c51868e282862702071232312a0a3882f188e021c39b0c43808e191c62000070aa230f202384661872021c1b60c35828e09c0619020702fc30ba1a3808f1856121bfcb0c278c8dfa846120806fb7030825237cca183a321bdef0c199e8debb860b1206f3e2304aaa37908181e621bc168c0bb88ddce06042006ec7a3013223754a1802a21ba310bfdda8dcdf85fd3206e52a2fdbba371a817e6f21b85b8bf0048dbf2c5f64806ddc82fa47236dfd17cb521b67f0be2368db0685ef6206d64e2f6d4a36a3817afc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page98Checked : PLift (fastPage primes 18 17 1550561 114752 223548 page98Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page98 (anchor : OMA.PrimePopulation.oddCount 1550561 = 223548) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page98Data i)) =
      rowCount (packedEvent page98Data i) := by
  exact fastPage_sound (width:=114752) (bound:=5000) (base:=1550561) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page98Checked.down

private theorem page98Good : GoodPage page98Data := by
  have anchor : oddCount 1550561 = 223548 := by exact page97Good 63 (by decide)
  exact (page98 anchor)

private def page99Data : ℕ := 0x1f1578d9cb08f86906cc8007c1603655423dfb51b23421ef5a0d8df28f77086c52207b986361a5a3dbd01b05d21ed728d7f3c8f67a86bdc807b1cc35df923d7f21ae8721eb870d708e8f58606b67207aa6035a4ea3d42e1acb221e99a0d61e88f49106af2007a28e356a623d0591aade21e7b20d534a8f398c6a7d2079ae8352ffa3cc8d1a90b21e5cd8d44b48f2ae06a08807938034f5b23c8c91a73921e3ec0d36268f1bb069942078bfa34bb8a3c50a1a56821e2058d27a08f0c7c6920007843c3481823c1241a39821e0140d19228efcb468ac2077c6634479a3bd3b1a1c921de248d0aac8eed64683880774be340dd23b95c19ffb21dc360cfc3e8edda867c52076cea33d42a3b57819e2e21da458cedd88ece4467520076532339aa23b1ad19c6221d8558cdf7a8ebf0466df2075d8833613a3adb419a9721d6668cd1248eafc8666c807560a3327f23aa18198cd21d4940cc2d68ea0dc65fa2074e6c32eeca3a64a197042

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page99Checked : PLift (fastPage primes 18 17 1665313 118848 238944 page99Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page99 (anchor : OMA.PrimePopulation.oddCount 1665313 = 238944) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page99Data i)) =
      rowCount (packedEvent page99Data i) := by
  exact fastPage_sound (width:=118848) (bound:=5000) (base:=1665313) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page99Checked.down

private theorem page99Good : GoodPage page99Data := by
  have anchor : oddCount 1665313 = 238944 := by exact page98Good 63 (by decide)
  exact (page99 anchor)

private def page100Data : ℕ := 0x211250e8cd09085287448008409c3a14c241f441d02c220f220e7d929074d473ce208388639d7da41b501ce45220d238e6e5c90650c73548083082399b12417431cc5f220b238e5f2e90551872db20828c4395e6a413681ca7a2209338e5008904544726200820be3921e240f681c8962207380e40ea9035cc71e920818c838e57a40b551c6b322052a0e31d4902534717080810a438a932407561c4d122032e8e22c690157070f820808ae386d0a403491c2f02201250e13c0900538708000800a83831023ff5b1c11021ff240e04c28ff5147008207f89037f51a3fb491bf3121fd290df5cc8fe5206f90807f09c37b9523f76b1bd5321fb3b8de6de8fd5ec6f19207e910377daa3f3931bb7621f9470dd7f88fc65c6ea2007e10e3742223ef8e1b99a21f7470dc91a8fb6246e2b207d8ee3706ba3eb7a1b7bf21f53d0dba448fa5c86db4807d10836cb723e7861b5e521f3428dab768f96246d3e207c92636904a3e3a91b40c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page100Checked : PLift (fastPage primes 18 17 1784161 122944 254639 page100Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page100 (anchor : OMA.PrimePopulation.oddCount 1784161 = 254639) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page100Data i)) =
      rowCount (packedEvent page100Data i) := by
  exact fastPage_sound (width:=122944) (bound:=5000) (base:=1784161) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page100Checked.down

private theorem page100Good : GoodPage page100Data := by
  have anchor : oddCount 1784161 = 254639 := by exact page99Good 63 (by decide)
  exact (page100 anchor)

private def page101Data : ℕ := 0x231db0f84f0918ad87c08008c3563df442460a21ef24222fd10f7532917a747b8a208bb123db55a45c781ed2d222db38f657c9169507b0c808b2963d7692458431eb37222b988f55ce9158c07a8f208aa503d37ea4541f1e94222298a0f46289148247a12008a2223cf962450021e74e2227838f368a91383479952089a1e3cbafa44c031e55b22257c8f26f49127b8791880891e03c7cb2447f81e36922237c0f1766911804789c20889e03c3e8a443e91e17822216d0f07e0910750782000881ae3c008243fcc1df88221f610ef86290f6ec77a4208796e3bc29a43bb21dd99221d548ee8ec90e668772880871483b84d2437ab1dbab221b498ed97e90d62476ad20868fe3b472a433821d9be22193e0eca1890c5e47632008610a3b09a242f861d7d22217408ebaba90b5f475b720858f43acc3a42b861d5e722153f0eab6490a5d8753c80850da3a8ef2427711d3fd2213390e9c169095dc74c220848d63a51ca423641d2142

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page101Checked : PLift (fastPage primes 18 17 1907105 127040 270922 page101Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page101 (anchor : OMA.PrimePopulation.oddCount 1907105 = 270922) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page101Data i)) =
      rowCount (packedEvent page101Data i) := by
  exact fastPage_sound (width:=127040) (bound:=5000) (base:=1907105) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page101Checked.down

private theorem page101Good : GoodPage page101Data := by
  have anchor : oddCount 1907105 = 270922 := by exact page100Good 63 (by decide)
  exact (page101 anchor)

private def page102Data : ℕ := 0x2535d1085109296808408009492e41f3c24a39120f1c2251451074d29285c0838620940c041b2da49f4e20d15224f1a90649c9274c88304809383e41721249b1920b0f224d0c10546e92642082832092ffc41316a496f12090a224af6104448925368820200927a040f0e2492bd207062248d090342a92428481812091f0840b07a48e8a205032246bd9024149231e0810080916d840703248a5a203012244a810140692212080802090e7a40300a4862820100224289900400921028800000906083ff002481f11ff002240690ff40291fefc7f80208fd7a3fb01a47dbb1fd01223e5b0fe40c91ee547f00808f50c3f7052479711fb03223c308fd41e91dd6c7e81208ec983f30aa475401f906223a200fc43891cd1c7e02008e4763ef122471311f70a22381d0fb45a91bce07d83208dc4c3eb1ba46d131f50f2236098fa48491ac2c7d04808d3f83e7272468f91f3152233f18f94b6919b907c86208cba03e334a464bb1f11c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page102Checked : PLift (fastPage primes 19 18 2034145 131136 287670 page102Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page102 (anchor : OMA.PrimePopulation.oddCount 2034145 = 287670) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page102Data i)) =
      rowCount (packedEvent page102Data i) := by
  exact fastPage_sound (width:=131136) (bound:=5000) (base:=2034145) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page102Checked.down

private theorem page102Good : GoodPage page102Data := by
  have anchor : oddCount 2034145 = 287670 := by exact page101Good 63 (by decide)
  exact (page102 anchor)

private def page103Data : ℕ := 0x275e6118d3093ab108c48009d3404613424e886230142273ba917c729399688bc2209ca7e45d05a4e43222dfd22718a116bbc9387b88b3c809c1c2458d924dfcc22be7226f52915b0e9376588ab7209b90e454aea4db70229d2226d2f914a689365408a32009b0764508624d72c227be226b0c9139ca93544889ad209a81044c5fa4d2e7225ab2268ea91293493430889288099f6c4483b24ce97223992266bc1118a693318888a4209968e44418a4ca392218822648e91082093203888200098de243ff824c5e121f7822626510f7a2930eec879c209852a43bd9a4c17021d6922603490e72c92fd1887188097c5e437bd24bd0f21b5b225dfe90d6be92eb5c869520973ac433a2a4b8ba2194e225bda90c65892daa886120096b2442f8a24b48b217422259bb90b5fa92c98c858f209629242b73a4b02e2153722579410a5a492b850850c8095a1a4275f24abfd2132d22557690955692a7a0848a20951b24234ca4a7c4211242

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page103Checked : PLift (fastPage primes 19 18 2165281 135232 304826 page103Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page103 (anchor : OMA.PrimePopulation.oddCount 2165281 = 304826) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page103Data i)) =
      rowCount (packedEvent page103Data i) := by
  exact fastPage_sound (width:=135232) (bound:=5000) (base:=2165281) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page103Checked.down

private theorem page103Good : GoodPage page103Data := by
  have anchor : oddCount 2165281 = 304826 := by exact page102Good 63 (by decide)
  exact (page103 anchor)

private def page104Data : ℕ := 0x29946129d5094c5e894c800a60b44a52c252f342520c22970a128c1294b3c4943e20a57c04a0dda52ab724fe52294cd927adc94a22c93b480a4eac49c9125262e24dbf22928b1269ae94903c932b20a45d249846a521cc24b9a229058125888947e7092a200a3cda493fe251d4e24976228e1792476a946c84921920a341848fb7a518ec24753228be3123654945af4919080a2b4248b73251489245312289b392254694494c910820a228248730a510272431022878b1214409437e0908000a198a482f0250bb4240f022854f1203429425fc8ff820a10b847eb1a5074823ed122831b91f24c94145c8f7080a07ec47a752502db23cb32280e891e15e94028c8ee9209fef44763aa4fe6123a96227ea311d07893f0948e62009f6104720224f9ec2387a227c7311bf9a93df6c8ddb209ed7a46dcba4f5a72365f227a4811aec493cdf48d54809e4d64699724f14423445227816119df693bc908cce209dc1446564a4ece22322c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page104Checked : PLift (fastPage primes 19 18 2300513 139328 322508 page104Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page104 (anchor : OMA.PrimePopulation.oddCount 2300513 = 322508) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page104Data i)) =
      rowCount (packedEvent page104Data i) := by
  exact fastPage_sound (width:=139328) (bound:=5000) (base:=2300513) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page104Checked.down

private theorem page104Good : GoodPage page104Data := by
  have anchor : oddCount 2300513 = 322508 := by exact page103Good 63 (by decide)
  exact (page104 anchor)

private def page105Data : ℕ := 0x2bdaf13b57095e8f49d8800af21e4eb242577f52750422bb6693a3b295d6bc9cfa20ae9004e6b5a57361272cd22b9171391fc95c4489c6c80adfb24e249256ebb2709722b6cf13804e95b1c49bdf20ad6b24dddea56a4026e6222b490936ea8959fd09b5200acda44d9762565a726c2e22b240935d0a958d949ac520ac4764d50fa5611c269fb22afff134b74957b289a3880abb524d0ab255c92267c922adb71339e695695099ac20ab2644cc48a5580d2659822ab75132860955708992000aa9464c7e82553882636822a9381316e295452c989420aa05e4c389a54f152613922a6f393056c9532f4980880a972e4bf2d254a7125f0b22a4ac92f3fe9520a8977d20a8df64bad2a545df25cde22a25f12e298950e8496f200a84e84b67a25415425ab222a01c92d13a94fc50966720a7bf04b223a53cce25887229ddc12bfe494ea6c95dc80a72ec4adcf25386c2565d229b9992ae9694d818955220a69b44a97ca533b4254342

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page105Checked : PLift (fastPage primes 19 18 2439841 143424 340620 page105Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page105 (anchor : OMA.PrimePopulation.oddCount 2439841 = 340620) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page105Data i)) =
      rowCount (packedEvent page105Data i) := by
  exact fastPage_sound (width:=143424) (bound:=5000) (base:=2439841) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page105Checked.down

private theorem page105Good : GoodPage page105Data := by
  have anchor : oddCount 2439841 = 340620 := by exact page104Good 63 (by decide)
  exact (page105 anchor)

private def page106Data : ℕ := 0x2e2f014d5909712a8a68800b870a5331c25c245298fc22e08d94c35296ffdca5f620b7d8a52e8da5bd9e296b522de3694b11c96ecc8a56480b742252a0125b8db2946f22dbd9949eee96da54a4d320b6aca52576a5b4482922a22d98b948cc896c7b8a44200b6176520ee25af7a28fe622d731147aaa96b4e0a3b120b581051c67a5aadd28da322d4db14689496a240a32080b4eca517e325a63b28b6122d285145686968f70a29020b455c51360a5a18d2892022d030944480967d1ca20000b3c3450ee0259ceb286e022cde2943282966a34a17020b32c450a61a5984d284a122cb9294208c9657f0a0e080b299e505e52593a32826322c93d940e9e964598a05120b205c5016aa58f012802622c6e813fcb89632909fc200b16fa4fcf2258a5927dea22c49893eada9620149f3320b0da84f87ba585bd27baf22c24213d904960d4c9ea480b04564f4072581072797522bff193c73695fb0c9e1620afb584ef94a57c822773c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page106Checked : PLift (fastPage primes 19 18 2583265 147520 359262 page106Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page106 (anchor : OMA.PrimePopulation.oddCount 2583265 = 359262) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page106Data i)) =
      rowCount (packedEvent page106Data i) := by
  exact fastPage_sound (width:=147520) (bound:=5000) (base:=2583265) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page106Checked.down

private theorem page106Good : GoodPage page106Data := by
  have anchor : oddCount 2583265 = 359262 := by exact page105Good 63 (by decide)
  exact (page106 anchor)

private def page107Data : ℕ := 0x308e195fdb0984254afc800c1edc57d14260e332bdf423067c95eaf2982f10af3220c152257865a609642bb9d23041915d83c981c10ae9c80c0b92573b92604832b9472301ae15c58e9808b0ae0720c01d856f0ea5ffb02b6f222ff3815b2e897f4e4ad7200bf82256a6625fae12b49e22fcd515a04a97e220acdd20beea2565bfa5f6262b24b22fa79958db497cf2cac4880be53e5611b25f17c2aff922f821157b2697bc24abb420bdbb855c78a5ecb32ada822f5c59568a097a930ab2000bd250557d825e7f52ab5822f36115562297966caa8c20bc8ca55339a5e3272a90922f10a9543ac978378a9f880bbf3854e9d25de722a6bb22ee9f95313e97706ca96520bb5dc54a02a5d9d22a46e22ec53951ed8975d6ca8d200bac665456a25d5132a22222e9f9950c7a974aeca83f20ba342540d3a5d06b29fd722e79c94fa24973828a7ac80b99b653c3f25cbb029d8d22e53f14e7d697256ca71a20b9056537aca5c70f29b442

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page107Checked : PLift (fastPage primes 19 18 2730785 151616 378336 page107Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page107 (anchor : OMA.PrimePopulation.oddCount 2730785 = 378336) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page107Data i)) =
      rowCount (packedEvent page107Data i) := by
  exact fastPage_sound (width:=151616) (bound:=5000) (base:=2730785) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page107Checked.down

private theorem page107Good : GoodPage page107Data := by
  have anchor : oddCount 2730785 = 378336 := by exact page106Good 63 (by decide)
  exact (page107 anchor)

private def page108Data : ℕ := 0x32fe1172dd09979f0b94800cba865c90c265c152e3ec232d6f171a9299666cb8ae20cb0b85c43da657282e185232af317075c995368b81480ca7345bf712652472df1f23288916f42e993f60b77b20c9d205baa6a64d4f2dcba23260616e108992ba8b6e200c93705b5de2648672da5623239b96cdea9917f4b64920c89b05b117a6439e2d7f323213216bad49904b8b5b080c80065ac53263ecb2d591231ec716a7c698f150b51820c76285a790a639de2d330231c4d9694c098dd7cb48000c6c225a2d02634d42d0d02319ce1681c298c9a8b3e820c625259e11a62ff32ce7123174e166ecc98b59cb35080c585e59955262afc2cc132314e7965bde98a278b2b920c4ed25949aa626292c9b62312759648f8988ee0b22200c451658fe226214c2c75a23101316361a987bc0b18b20c3b7c58b2ba61c8a2c4ff230da1162344986864b0f480c31cc586772617ab2c2a5230b3d161076985530b05e20c284c581c4a612e72c04c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page108Checked : PLift (fastPage primes 19 18 2882401 155712 397763 page108Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page108 (anchor : OMA.PrimePopulation.oddCount 2882401 = 397763) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page108Data i)) =
      rowCount (packedEvent page108Data i) := by
  exact fastPage_sound (width:=155712) (bound:=5000) (base:=2882401) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page108Checked.down

private theorem page108Good : GoodPage page108Data := by
  have anchor : oddCount 2882401 = 397763 := by exact page107Good 63 (by decide)
  exact (page108 anchor)

private def page109Data : ℕ := 0x357bc1865f09ab8ccc30800d59f66170426abc030ae42355441852329aa550c26a20d503261215a6a6df3086d2352cb983e7c9a9178c1cc80d464060d2926a1db305f723504f182ace9a7d9cc12f20d3c366083ea69cd730382234dc39817289a695cc09200d323e603562697cf3010e234b3c98038a9a54e0bff520d27ee5fe6fa692a02fe9b2348b197eff49a4088bf5880d1dcc5f98b268d992fc2923462b97dc669a2c3cbebc20d13a05f4a8a688932f9b82343ad97c8e09a1868be2000d09b45efc826838f2f74823413217b5629a04dcbd8420cffee5eae9a67eb52f4d9233eb417a1ec99f0c4bce880cf5e45e60d2679c92f26b233c45178e7e99dd4cbc4d20cec0e5e132a674c82effe2339c6977b1899c93cbbb200ce20c5dc5a266fd32ed922337471767ba99b560bb1720cd82c5d783a66ae02eb272334d397546499a1a8ba7c80cce5c5d2af2665eb2e8bd233251974116998db0b9e220cc4385cddca660fb2e6542

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page109Checked : PLift (fastPage primes 19 18 3038113 159808 417730 page109Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page109 (anchor : OMA.PrimePopulation.oddCount 3038113 = 417730) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page109Data i)) =
      rowCount (packedEvent page109Data i) := by
  exact fastPage_sound (width:=159808) (bound:=5000) (base:=3038113) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page109Checked.down

private theorem page109Good : GoodPage page109Data := by
  have anchor : oddCount 3038113 = 417730 := by exact page108Good 63 (by decide)
  exact (page109 anchor)

private def page110Data : ℕ := 0x3808c99a6109bff1ccd0800dfcea666fc26fd28332dc237deb9991d29bea30cc6620df27c661eda6f7eb33055237b59997d9c9bd5a0cbc480de84465ce126f2d832dcf2378c799696e9bc138cb2320dde14657d6a6edd132b4a2376421955489bace8ca8200dd3fe652ce26e8b6328c62373bf19412a9b98c4c9e120dc9ae64dc7a6e39032643237123992d149b8404c94080dbf84648c326de7b323c1236e8c9919069b6f5cc8a020db520643c0a6d94c32140236bfa1905009b5ad4c80000daae863ec026d42831ec023697118f1029b468cc76020da09a639c1a6cf1131c412366ea18dd0c9b3234c6c080d9680634c526c9ff319c323645798c91e9b1db0c62120d8c4c62fcaa6c4e3317462361cf98b5389b097cc58200d824c62ad226bfdd314ca235f4e98a15a9af540c4e320d780e625dba6bac23124f235cc2988d849ae120c44480d6e1c620e726b5c830fd5235a3e9879b69acd28c3a620d640c61bf4a6b0ba30d5c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page110Checked : PLift (fastPage primes 19 18 3197921 163904 438136 page110Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page110 (anchor : OMA.PrimePopulation.oddCount 3197921 = 438136) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page110Data i)) =
      rowCount (packedEvent page110Data i) := by
  exact fastPage_sound (width:=163904) (bound:=5000) (base:=3197921) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page110Checked.down

private theorem page110Good : GoodPage page110Data := by
  have anchor : oddCount 3197921 = 438136 := by exact page109Good 63 (by decide)
  exact (page110 anchor)

private def page111Data : ℕ := 0x3aa6c9aee309d4e10d74800ea46c6b8f42750db35bd423a7c11ad9729d3894d6a220e99846b3c5a74b713593d23a50c1ac4bc9d2324d5fc80e8efc6ae99274634356a723a2749ab00e9d0e60d55720e84886a96ea740fc35412239fdb9a9b689cf980d4b200e7a266a446273bbc3517e239d411a86ca9ce474d40d20e6f8c69f1fa7367534eeb239a8a9a72349ccf2cd36880e6512699fb27312d34c592397f59a5da69cba68d2c420e5aaa694d8a72c0f349c823955c9a49209ca5bcd22000e502468fb82726c8347382392bf9a34a29c90b8d17c20e459468a99a72170344a92390119a202c9c7b68d0d880e3b1a6857d271c403421b238d791a0bbe9c66a4d03520e30a668062a7170c33f8e238adc19f7589c5184cf9200e261667b4a2711cc33d0223884919e2fa9c3d28ceef20e1c0467633a70cbc33a772385bd19cea49c28dcce4c80e11b46711f27078c337ed23831c99ba569c13c8cdaa20e075666c0ca70261335642

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page111Checked : PLift (fastPage primes 19 18 3361825 168000 459033 page111Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page111 (anchor : OMA.PrimePopulation.oddCount 3361825 = 459033) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page111Data i)) =
      rowCount (packedEvent page111Data i) := by
  exact fastPage_sound (width:=168000) (bound:=5000) (base:=3361825) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page111Checked.down

private theorem page111Good : GoodPage page111Data := by
  have anchor : oddCount 3361825 = 459033 := by exact page110Good 63 (by decide)
  exact (page111 anchor)

private def page112Data : ℕ := 0x3d4df1c3e509ea194e1c800f4e1e70cec27a5c1385cc23d23a1c29129e8c74e11e20f436e7079da7a05b3832523cf819c13dc9e76b4e07480f38a470251279af43807f23ccd71bfeae9e617cdfcb20f2e1a6fd06a795b737dda23ca321be9889e4c10df2200f236c6f7be27906137b3623c7881bd46a9e36e4de7920f18b86f277a78b0a3789323c4d89bbf549e216cddd080f0dfa6ed332785a6375f123c22c1baa469e0bf0dd2820f034c6e7f0a780493735023bf7a1b95409df6b4dc8000ef8a46e2b0277b04370b023bcd59b80429de180dbd820eee046dd71a775b636e1123ba2c9b6b4c9dcc38db3080ee3646d83527707c36b7323b78d9b565e9db730da8920ed8ee6d2faa76b25368d623b4e89b41789da1d4d9e200ece5a6cdc22765e33663a23b2541b2c9a9d8d7cd93b20ec4166c88ba760be3639f23afb11b17c49d7800d89480eb97a6c357275b5a3610523ad041b02f69d62c4d7ee20eaeae6be24a7561235e6c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page112Checked : PLift (fastPage primes 19 18 3529825 172096 480473 page112Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page112 (anchor : OMA.PrimePopulation.oddCount 3529825 = 480473) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page112Data i)) =
      rowCount (packedEvent page112Data i) := by
  exact fastPage_sound (width:=172096) (bound:=5000) (base:=3529825) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page112Checked.down

private theorem page112Good : GoodPage page112Data := by
  have anchor : oddCount 3529825 = 480473 := by exact page111Good 63 (by decide)
  exact (page112 anchor)

private def page113Data : ℕ := 0x400429d96709ffc78ec8800ffb9c762e427fc6f3b0c423fd8c1d80b29fe718ebda20ff0e075d75a7f7073ae0d23fad21d6afc9fd118eb2c80fe5e87580927f18e3ab5723f8149d554e9fbb14ea7f20fdad47529ea7ec143a8a223f5571d3fa89fa554e9d200fcfea74d3627e6993a5ee23f2979d2a0a9f8f5ce92520fc504747cfa7e1343a33b23efd71d14749f79b0e87880fba347426b27dbb73a08923ed251cfee69f63a0e7cc20faf0673d08a7d61f39dd823ea651ce9609f4de0e72000fa430737a827d0d539b2823e7bb9cd3e29f3870e67420f996873249a7cb4e3987923e4fa1cbe6c9f222ce5c880f8e8472ced27c5f9395cb23e2451ca8fe9f0cf4e51d20f83ca72792a7c0883931e23dfa21c93989ef7bce47200f79327223a27bb2a3907223dcea9c7e3a9ee224e3c720f6e7671ce3a7b5f138dc723da479c68e49eccace31c80f63b27178f27b07638b1d23d78d9c53969eb710e27220f58ce7123ca7ab05388742

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page113Checked : PLift (fastPage primes 19 18 3701921 176192 502206 page113Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page113 (anchor : OMA.PrimePopulation.oddCount 3701921 = 502206) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page113Data i)) =
      rowCount (packedEvent page113Data i) := by
  exact fastPage_sound (width:=176192) (bound:=5000) (base:=3701921) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page113Checked.down

private theorem page113Good : GoodPage page113Data := by
  have anchor : oddCount 3701921 = 502206 := by exact page112Good 63 (by decide)
  exact (page113 anchor)

private def page114Data : ℕ := 0x42c809ef690a15e5cf788010ac587badc2854d33dcbc2429bb1ee052a14878f6d6210a1727b54da84f603d9f52427059eca1ca1328cf624810966c7afc12849c23d72f24242d1eb3eea11bdcf5732108b1c7aa36a8442e3d46a24216d9e9dc8a1059cf4c201080227a4ae283eb83d1a6241ea69e87aaa0efd0f411210751e79f27a839353cee3241be41e7194a0d96cf36081069e0799a328339e3cc2124191a1e5b86a0c378f2b02105f0679420a82e113c9602416599e4580a0ad38f20001053e078ea028288a3c6a02413951e2f82a09700f15021048c878921a8230d3c3e12410d59e198ca08120f0a08103db8783a5281d773c123240e049e039ea06ac8eff1210329477e2aa817e93be66240b451dedb8a0545cef420102744778b228124a3bbaa24087b9dd7daa03e70ee932101c587733ba80cd03b8ef2405b21dc204a02800ede4810114676dc728075f3b6352402fb1dac36a01258ed36210067276854a801df3b37c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page114Checked : PLift (fastPage primes 19 18 3878113 180288 524421 page114Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page114 (anchor : OMA.PrimePopulation.oddCount 3878113 = 524421) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page114Data i)) =
      rowCount (packedEvent page114Data i) := by
  exact fastPage_sound (width:=180288) (bound:=5000) (base:=3878113) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page114Checked.down

private theorem page114Good : GoodPage page114Data := by
  have anchor : oddCount 3878113 = 524421 := by exact page113Good 63 (by decide)
  exact (page114 anchor)

private def page115Data : ℕ := 0x459b6205eb0a2c7a102c801160f8814d428af06409b42456d7a047f2a2b0e90212211558c80f25a8a960406dd24540520313ca29a99015c8114a6e8097928a3d34040724513a201a8ea283d500a72113f20803cea89e2a40132244e61a003e8a26d64fff201133cc7fe262898733fe5e244b8a1fed4aa2568cff3d21128987f87fa892eb3fb8b2448b61fd6b4a23fd4fe888111d147f2db288d2d3f8b92445e21fc026a22954fdd421111d87ed38a887833f5e82443071fa9a0a212a4fd2001106967e7982881db3f3182440361f9322a1fbfcfc6c210fb267e1f9a87c3c3f049243d6b9f7caca1e5d4fbb8810f01c7dc5d28769d3ed7b243a939f663ea1cef0fb05210e4c07d6c2a870fa3eaae2437c69f4fd8a1b860fa52010d9607d12a286b4f3e7e22434f61f397aa1a1c0f99f210ce147cb93a865ae3e5172432201f2324a18b5cf8ec810c2c87c5ff285ffe3e24d242f4e1f0cd6a1750cf83a210b7e47c06ca85a693df842

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page115Checked : PLift (fastPage primes 19 18 4058401 184384 547073 page115Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page115 (anchor : OMA.PrimePopulation.oddCount 4058401 = 547073) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page115Data i)) =
      rowCount (packedEvent page115Data i) := by
  exact fastPage_sound (width:=184384) (bound:=5000) (base:=4058401) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page115Checked.down

private theorem page115Good : GoodPage page115Data := by
  have anchor : oddCount 4058401 = 547073 := by exact page114Good 63 (by decide)
  exact (page115 anchor)

private def page116Data : ℕ := 0x487ed21ced0a439bd0e4801219fc870cc290b7f437ac248509a1b792a422c90d8e2120e8686afda905bc434c524822ca1a05ca40b750cd481202e086531290005431df247f4aa1892ea3f4c90c1b211f73e85f66a8fa3942efa247c5ea17208a3dd1d0b62011eb7c8599e28f45342c16247978a15aeaa3c5f10aa9211e028853d7a8ee9c42933247692a143d4a3aeb909f0811d46884e1328e8c3426512473a5a12cc6a3975d0938211c8c084850a8e2ec423702470ca2115c0a3805d0880011bd6c8429028dd3842090246dd9a0fec2a3694d07c8211b1ca83cd1a8d76941db1246b0220e7cca352590710811a6548371528d1ab41ad324681ea0d0dea33b2d06592119ac28315aa8cbf5417f6246543a0b9f8a323f905a20118efe82ba228c6214151a24625ea0a31aa30cd504eb21183b2825eba8c05f4123f245f76208c44a2f61d043481178108203728ba9c40f65245c91a07576a2dec5037e2116c9481a84a8b4d740c8c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page116Checked : PLift (fastPage primes 19 18 4242785 188480 570220 page116Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page116 (anchor : OMA.PrimePopulation.oddCount 4242785 = 570220) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page116Data i)) =
      rowCount (packedEvent page116Data i) := by
  exact fastPage_sound (width:=188480) (bound:=5000) (base:=4242785) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page116Checked.down

private theorem page116Good : GoodPage page116Data := by
  have anchor : oddCount 4242785 = 570220 := by exact page115Good 63 (by decide)
  exact (page116 anchor)

private def page117Data : ℕ := 0x4b6d5a346f0a5b0f11a08012d5788cec4296945466a424b3dfa32f32a598d1194a212c9668c8d5a96337463ad24b0e8a3177ca5812d188c812bd988c2e9295d4f460b724ade4a2ffcea5694917cf212b1a88bcfea9576445dc224aaf922e828a552091712012a5f48b71629516e45ace24a7fd22d08aa53a3516552129a2c8b12fa94bac457db24a51b22b8f4a522ed15988128e8c8ab4b2945c2454e924a220a2a166a50b3914dc21282948a568a93fd7451f8249f312289e0a4f41d142001276f889f88293a0544f08249c47a27262a4dca913642126b48899a9a9343644c19249966225aeca4c5e112a88125ff6893cd292e7f4492b24967aa2437ea4ade911ed212541088df2a928974463e249399222c18a4970d113201248928881a2922dc443522490ae2214baa47fb110772123cc088243a91cec44067248db7a1fd64a467c50fbc812312687c6f29171043d7d248ace21e616a450c90f0221225808769ca9113c43a942

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page117Checked : PLift (fastPage primes 19 18 4431265 192576 593882 page117Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page117 (anchor : OMA.PrimePopulation.oddCount 4431265 = 593882) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page117Data i)) =
      rowCount (packedEvent page117Data i) := by
  exact fastPage_sound (width:=192576) (bound:=5000) (base:=4431265) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page117Checked.down

private theorem page117Good : GoodPage page117Data := by
  have anchor : oddCount 4431265 = 593882 := by exact page116Good 63 (by decide)
  exact (page117 anchor)

private def page118Data : ℕ := 0x4e6a6a4c710a72f31260801394a692ebc29c8c64969c24e3a724aed2a717312546213889a928ada9c2d94939524e0aa24969ca6ff2d24848137c56922a129bca44908f24dd8ca47e6ea6e6c523c3213704891c96a9b6aa48d8a24da94a46648a6cea92302013642a9168e29b0a748a8624d793244e2aa6b6c52241213584a91087a9aa9c4878324d48fa43614a69e7521808134c4890a8329a4ad4848124d18ca41e06a6869120c0213406090480a99ebb4818024ce9ca40600a66ed52000013347e8fe802998cd47e8024cba6a3ee02a657491f4021328b68f881a992de47b8124c8aea3d60ca63f951e808131cc08f285298cf74788324c5bea3be1ea628091dc121310f48ec8aa987014758624c2b6a3a638a60fe91d0201304e68e6922980fc4728a24bfbfa38e5aa5f83d1c43212f9148e09ba97b1f46f8f24bcc7237684a5e0451b84812ed3a8daa729751d46c9524b9d5a35eb6a5c8951ac6212e1768d4b4a96f3d4699c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page118Checked : PLift (fastPage primes 19 18 4623841 196672 617899 page118Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page118 (anchor : OMA.PrimePopulation.oddCount 4623841 = 617899) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page118Data i)) =
      rowCount (packedEvent page118Data i) := by
  exact fastPage_sound (width:=196672) (bound:=5000) (base:=4623841) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page118Checked.down

private theorem page118Good : GoodPage page118Data := by
  have anchor : oddCount 4623841 = 617899 := by exact page117Good 63 (by decide)
  exact (page118 anchor)

private def page119Data : ℕ := 0x51730264f30a8b36132480145696990b42a29c54c794251416263672a89a9531822144a3898a85aa239c4c47d251106a61dbca8827530bc8143e40984592a1d904c167250e0ba6050ea86a3d2ff7214321a97e2eaa17894be52250b05a5ec68a852192f3201425d0978062a116c4bb3e2507f5a5d3caa839a92e6d21419d2971dfaa0b704b82b2504ed25bb34a821592da88140da696bbb2a05514b5192501eaa5a2a6a809192ce4214017a96598a9ff464b20824fee9a58a20a7f13d2c20013f59295f7829f9514aef824fbda2571a2a7d8e12b5c213e95a95959a9f31c4abe924f8cca5592ca7c0312a98813dd249533d29ed0e4a8db24f5ca2540bea7a85529d5213d13294d22a9e71a4a5ce24f2c7252858a790192912013c4e69470a29e0eb4a2c224efb7250ffaa777c5284f213b8c6940f3a9daf949fb724ecbf24f7a4a75fd9278c813ace093adf29d4f549cad24e9b2a4df56a7478126ca213a0c2934cca9cede499a42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page119Checked : PLift (fastPage primes 19 18 4820513 200768 642381 page119Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page119 (anchor : OMA.PrimePopulation.oddCount 4820513 = 642381) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page119Data i)) =
      rowCount (packedEvent page119Data i) := by
  exact fastPage_sound (width:=200768) (bound:=5000) (base:=4820513) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page119Checked.down

private theorem page119Good : GoodPage page119Data := by
  have anchor : oddCount 4820513 = 642381 := by exact page118Good 63 (by decide)
  exact (page119 anchor)

private def page120Data : ℕ := 0x548c6a7df50aa402d3ec80151ce69f4ac2a8cea4f98c2545a727c612aa27193dfe21510589ee5daa869a4f665254286a7acdcaa0dc53d3481503c29e8112a80444f33f253f612793aea9f4ad3c6b214f74a9e1c6aa7a094f01a253c3f277a88a9dc313ba2014ead49db7e2a73da4ecf6253922a7616aa9c2b53ad9214de629d537aa6d9c4e9d3253610a74854a9aa613a10814d2149cef32a67884e6b12532f8a72f46a991613948214c5809c8b0aa612f4e390252fd1271640a978913880014b92a9c2702a5b004e070252cafa6fd42a95f9537b8214acca9bc31aa54d34dd512529a326e44ca9475536f0814a09c9b5f52a4ecc4da3325269fa6cb5ea92ef9362921494669afbaaa48b24d716252396a6b278a91615356201488009a9822a42784d3fa252074a6999aa8fd75349b2147b8a9a34baa3c4c4d0df251d602680c4a8e50133d48146f5e99d172a361a4cdc5251a4da667f6a8cc51330e2146316996e4aa2ff84caac2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page120Checked : PLift (fastPage primes 19 18 5021281 204864 667232 page120Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page120 (anchor : OMA.PrimePopulation.oddCount 5021281 = 667232) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page120Data i)) =
      rowCount (packedEvent page120Data i) := by
  exact fastPage_sound (width:=204864) (bound:=5000) (base:=5021281) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page120Checked.down

private theorem page120Good : GoodPage page120Data := by
  have anchor : oddCount 5021281 = 667232 := by exact page119Good 63 (by decide)
  exact (page120 anchor)

private def page121Data : ℕ := 0x57b5aa97770abd44d4b88015e6f4a5aa42af1ec52c84257828a95db2abba8d4aba215d9fca5435aaeb715294d2574f62943fcaba13949ec815cd76a4dc92ae519526172571c2a92a4eab8805491f215c0d6a475eaaded3522e2256ea82910a8ab6f0d4852015b470a40f62ad89f51fae256b8428f70aab55f14785215a7d2a3a8faad26351c7b25685da8dd74ab3c8946b88159b06a342b2acbee5194925652d28c3e6ab230d45ec2158e4ca2dc8aac579516182561f4a8aa60ab095145200158188a27682abf27512e8255ecaa890e2aaf01d445421574c6a2109aab8d650fb9255ba2a8776caad6e543888156864a1aad2ab29650c8b255882285dfeaabdd142bd2155be8a1452aaac545095e255561284498aaa4c541f20154f14a0dfa2aa5fa50632255232a82b3aaa8b91412721542c0a07a3aa9fcb50307254f1ba811e4aa728d405c815362ea014f2a99754ffdd254bf527f896aa595d3f92215296e9fafcaa932b4fcb42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page121Checked : PLift (fastPage primes 19 18 5226145 208960 692621 page121Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page121 (anchor : OMA.PrimePopulation.oddCount 5226145 = 692621) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page121Data i)) =
      rowCount (packedEvent page121Data i) := by
  exact fastPage_sound (width:=208960) (bound:=5000) (base:=5226145) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page121Checked.down

private theorem page121Good : GoodPage page121Data := by
  have anchor : oddCount 5226145 = 692621 := by exact page120Good 63 (by decide)
  exact (page121 anchor)

private def page122Data : ℕ := 0x5aeaaab1790ad6e895888016b408ac29c2b58785607c25ab6c2afd52ad552157b6216a76cabc0dab520a55d3525a8332ae31cad3b1956e48169a5cab5812b4b9e559ef25a4fcaac8eead219956132168da6aaef6ab4534556aa25a1c72aaec8ad07e1554201680a4aa86e2b3eae55366259e862a94aaacedb5547121673a8aa1e7ab382255023259b462a7a94acd3e953a081666f8a9b632b31f054ce1259822aa6086acbac552d02165a12a94e0ab2b60549a02594eb2a4680aca0c552000164d24a8e602b24f9546602591a92a2c82ac86c551302164018a87e1ab1e7154321258e6c2a128cac6d155060816335ca81652b182153fe3258b4a29f89eac53e94f9121626b4a7aeaab11cb53ca6258815a9deb8ac3aa14ec20161a16a74722b0b6a5396a2584eda9c4daac20b54df32160d1ca6dfbab05045362f2581b0a9ab04ac06e54d24816005ea67872afe9c532f5257e76a99136abed754c56215f386a6114aaf84052fbc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page122Checked : PLift (fastPage primes 19 18 5435105 213056 718517 page122Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page122 (anchor : OMA.PrimePopulation.oddCount 5435105 = 718517) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page122Data i)) =
      rowCount (packedEvent page122Data i) := by
  exact fastPage_sound (width:=213056) (bound:=5000) (base:=5435105) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page122Checked.down

private theorem page122Good : GoodPage page122Data := by
  have anchor : oddCount 5435105 = 718517 := by exact page121Good 63 (by decide)
  exact (page122 anchor)

private def page123Data : ℕ := 0x5e2d72cbfb0af104565c801784d4b2c942bc0c95957425df9d2ca4f2aef5f964f221777a6b25e5abba2d5921d25dc4e2c8a3caedbf5641c8176ac0b1f392bb3ba58ec725d9042c6f8eaec15163472175daab188eabad4658b7225d5cdac54e8aea7856272017504cb11e62ba66e5881e25d26bac3a4aae8ce1619d217431eb0b3fab9ff0584cb25cf29ac1fb4ae72a160c8817361eb049b2b996b5817925cbd9ac0526ae584d5ff421728c2afdf8ab92b457e2825c88d2beaa0ae3e395f200171bc4af7582b8c4057ad825c54eabd022ae24415e4c2170ed4af0b9ab85c15778925c20cabb5acae09795d788170198aea1d2b7f1d5743b25bec8ab9b3eadeff15ca5216f49cae382ab78b2570ee25bb8dab80d8add5e95bd2016e788adcea2b723856da225b850ab667aadbbf95aff216dacaad653ab6bcc56a5725b5182b4c24ada2195a2c816cdeeacfbf2b65675670d25b1dc2b31d6ad8861595a216c0deac92cab5ed7563c42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page123Checked : PLift (fastPage primes 19 18 5648161 217152 744789 page123Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page123 (anchor : OMA.PrimePopulation.oddCount 5648161 = 744789) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page123Data i)) =
      rowCount (packedEvent page123Data i) := by
  exact fastPage_sound (width:=217152) (bound:=5000) (base:=5648161) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page123Checked.down

private theorem page123Good : GoodPage page123Data := by
  have anchor : oddCount 5648161 = 744789 := by exact page122Good 63 (by decide)
  exact (page123 anchor)

private def page124Data : ℕ := 0x617deae6fd0b0b839734801858dcb988c2c2ac65cb6c26148e2e5492b09d75726e2184b4cb91bdac240c5c805261131ae395cb082b971948183df0b8af12c1d535c49f260ddf2e1e2eb0686d70bb21830f0b8426ac16cb5c13a260a96ae0308b04da56fe20182384b7d5e2c10195bdd6260733ade7eab033116f092181664b7697ac09795ba732603e7adccd4b018cd6e308180920b6fd32c02f05b71126009badb1c6affe396d58217fbf4b6910abfc4a5b3b025fd4a2d96c0afe38d6c80017ee6ab62502bf5a75b05025f9ef2d7bc2afc8c96ba8217e116b5b91abeee85acf125f69cad60ccafae796ad0817d402b54d52be83f5a99325f352ad45deaf93bd69f9217c672b4e1aabe1955a63625f003ad2af8af79b16922017b994b47622bdb285a2da25ecbbad101aaf5f8d684b217ac5cb40ababd48959f7f25e9702cf544af444567748179f06b39f72bcde759c2525e6242cda76af2ab1669e21791f0b3344abc761598cc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page124Checked : PLift (fastPage primes 19 18 5865313 221248 771502 page124Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page124 (anchor : OMA.PrimePopulation.oddCount 5865313 = 771502) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page124Data i)) =
      rowCount (packedEvent page124Data i) := by
  exact fastPage_sound (width:=221248) (bound:=5000) (base:=5865313) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page124Checked.down

private theorem page124Good : GoodPage page124Data := by
  have anchor : oddCount 5865313 = 771502 := by exact page123Good 63 (by decide)
  exact (page124 anchor)

private def page125Data : ℕ := 0x64dce3027f0b267a581080193074c06842c967a60264264a63300c32b24c55802a21922bcbff95ac8fa25feed2646fcaff07cb2314d7f4c8191552bf8a92c88f85fb7726439f2fd4ceb216c57e6f219080abf1beac823b5f80226403dafb928b1fb197d92018fa5ebead62c7b935f48e263cf0af9d8ab1e0b17cb5218ecf4be3efac74d45f11b263992af81f4b1c5d97bd8818df78bdd0b2c6e115eda92636352f6666b1aae97afc218d224bd628ac674b5ea382632cd2f4ae0b18f797a20018c48abcf482c608a5e6c8262f7b2f2f62b174417944218b6a4bc869ac599b5e359262bfb2f13ecb159697868818a968bc18d2c53115dfeb2628b22ef87eb13e59778d2189bbebbab2ac4c2d5dc7e26253b2edd18b1235d76b20188e3cbb3da2c45735d9122621df2ec1bab1087575d721880f4bad03ac3eda5d5a7261e902ea664b0edad74fc8187384ba62f2c38015d23d261b2cae8b16b0d2cd7422218662ab9f5cac31595ced42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page125Checked : PLift (fastPage primes 19 18 6086561 225344 798653 page125Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page125 (anchor : OMA.PrimePopulation.oddCount 6086561 = 798653) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page125Data i)) =
      rowCount (packedEvent page125Data i) := by
  exact fastPage_sound (width:=225344) (bound:=5000) (base:=6086561) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page125Checked.down

private theorem page125Good : GoodPage page125Data := by
  have anchor : oddCount 6086561 = 798653 := by exact page124Good 63 (by decide)
  exact (page125 anchor)

private def page126Data : ℕ := 0x68473b1e810b41cd98f0801a0af4c767c2d03d163a5c268118b1cbd2b401ad8e26219fd76c6f6dacfd02636d5267dafb1af9cb3e6718d44819efbcc68612cf6246334f267a2fb1936eb3ca598c63219e1dec6156acef4862fca2676ca317748b3af818b82019d458c5a4e2ce86b62c46267361315b2ab394398aa1219c6c0c5347ace1a1628c3266ffab13f14b3791589c0819b94ac4c432cdadf62541266c9fb12306b35e6d88e0219abbac4540acd41b621c0266934b10700b3429188000199decc3e402ccd4161e402665be30eb02b327298720219902ac3741acc66561ac1266255b0cf0cb30bd586408198294c30452cbf8f61743265eeb30b31eb2f065856121974c4c294aacb8b6613c6265b7b309738b2d4b98482019670ac22522cb1bf6104a2657fab07b5ab2b94183a32195924c1b5bacaae460ccf26549db05f84b29da982c48194b7ac14672ca41660955265138b043b6b282dd81e62193e1ac0d74ac9d5e605dc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page126Checked : PLift (fastPage primes 19 18 6311905 229440 826268 page126Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page126 (anchor : OMA.PrimePopulation.oddCount 6311905 = 826268) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page126Data i)) =
      rowCount (packedEvent page126Data i) := by
  exact fastPage_sound (width:=229440) (bound:=5000) (base:=6311905) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page126Checked.down

private theorem page126Good : GoodPage page126Data := by
  have anchor : oddCount 6311905 = 826268 := by exact page125Good 63 (by decide)
  exact (page126 anchor)

private def page127Data : ℕ := 0x6bbe733b030b5d86d9d4801ae8b8ce8742d729d6735426b872b39372b5bc719c6221adad4ce145ad6baa66fbd26b4f03376bcb5a0a99b7c81acccecda192d64b066c2726b180b35a0eb584e59a9721abefecd2eead5de26689226ae06b33d68b5694d99b201ab130ccbc62d56dc664fe26aa983320cab54da198cd21aa35ecc49fad4ff86616b26a716330434b531d597e881a955ccbd7b2d48e965dd926a39932e7a6b515e9970421a8758cb658ad420965a4826a02132cb20b4f9f9962001a7974caf382d3aef656b8269ca732aea2b4de29953c21a6b90ca819ad34046532926992bb2922cb4c29d945881a5dccca0fd2d2d2f64f9b2695b9b275beb4a6d5937521a4ff2c99e2ad264464c0e269241b25958b48b01929201a41f8c92ca2d1f4064882268ebcb23cfab46f2591af21a3424c8bb3ad1864644f7268b573220a4b453b190cc81a2654c849f2d11676416d2687e1b20456b438018fea21a1882c7d8cad0a9b63de42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page127Checked : PLift (fastPage primes 19 18 6541345 233536 854247 page127Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page127 (anchor : OMA.PrimePopulation.oddCount 6541345 = 854247) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page127Data i)) =
      rowCount (packedEvent page127Data i) := by
  exact fastPage_sound (width:=233536) (bound:=5000) (base:=6541345) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page127Checked.down

private theorem page127Good : GoodPage page127Data := by
  have anchor : oddCount 6541345 = 854247 := by exact page126Good 63 (by decide)
  exact (page127 anchor)

private def page128Data : ℕ := 0x6f474358050b79c5dabc801bcabed5c6c2de3926ad4c26f0e3356312b78069aade21bbca8d551daddc9c6a9a526ed6cb545dcb76465a9f481baed0d4dd12dd5a86a5ff26e9f2b528aeb7489da90b21ba0ced4686adce956a25a26e666350b88b72bd9a82201b925ad3f3e2dc75d69eb626e2cbb4ee6ab70f09a73921b840ed37f7adc04969b1326df3b34d154b6f259a65081b75d0d30b32db9256977126dbaeb4b446b6d665a56821b67a0d2970adb222693d026d823349740b6b999a48001b5966d22302daaf26903026d4a7347a42b69db1a39821b4b50d1af1ada3eb68c9126d115b45d4cb681c5a2b081b3d46d13b52d9ce6688f326cd91b4405eb665b9a1c921b2f40d0c7aad95df6855626ca09342378b64939a0e201b20f2d05422d8ebd681ba26c67e34069ab62cd99ffb21b12e8cfe0bad87ba67e1f26c2fab3e9c4b610619f1481b04c0cf6d72d809567a8526bf6ab3ccf6b5f45d9e2e21af6a6cefa4ad798d676ec2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page128Checked : PLift (fastPage primes 19 18 6774881 237632 882638 page128Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page128 (anchor : OMA.PrimePopulation.oddCount 6774881 = 882638) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page128Data i)) =
      rowCount (packedEvent page128Data i) := by
  exact fastPage_sound (width:=237632) (bound:=5000) (base:=6774881) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page128Checked.down

private theorem page128Good : GoodPage page128Data := by
  have anchor : oddCount 6774881 = 882638 := by exact page127Good 63 (by decide)
  exact (page128 anchor)

private def page129Data : ℕ := 0x72dd3b75870b96779ba8801cb04add2642e565d6e844272a41373ab2b94acdb99a21ca1eedcaf5ae4f206e48d2726a9371cfcb92e0db8ac81c9380dc3892e47f16e0d727231636ff4eb91181b7bf21c853edbc1eae40cf6dd22271f7eb6e1a8b8f47db6d201c7690db4b62e39846d96e271bdcb6c40ab8d6f5b5e521c67eedad4fae32286d5bb27182836a674b8ba85b4f881c5982da5eb2e2af26d2092714993688e6b89db9b40c21c4b40d9e88ae23ba6ce582710ffb66b60b880b5b32001c3cc0d97282e1c926caa8270d62364de2b863c9b23421c2e66d8fc9ae155c6c6f92709c6b6306cb84731b14881c202ed886d2e0e536c34b27064ab612feb82b35b05d21c1216d8112ae073e6bf9e2702bf35f598b80eb9af7201c03dad79ba2e001c6bbf226ff2cb5d83ab7f1e5ae8721bf564d7263adf8f16b84726fb9735bae4b7d539ad9c81be6f2d6b0f2df1c96b49d26f7fdb59d96b7b8f9acb221bd8e8d63bcadeabe6b0f42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page129Checked : PLift (fastPage primes 19 18 7012513 241728 911592 page129Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page129 (anchor : OMA.PrimePopulation.oddCount 7012513 = 911592) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page129Data i)) =
      rowCount (packedEvent page129Data i) := by
  exact fastPage_sound (width:=241728) (bound:=5000) (base:=7012513) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page129Checked.down

private theorem page129Good : GoodPage page129Data := by
  have anchor : oddCount 7012513 = 911592 := by exact page128Good 63 (by decide)
  exact (page129 anchor)

private def page130Data : ℕ := 0x767eab93890bb380dc98801d9852e4a5c2eca597243c276442b91a52bb1afdc89621d8a28e42cdaec326720752760a0b8fc1cbafdd1c7a481d7b54e3b412ebbd571caf275d01b8ddeebae0f9c6b321d6cd0e33b6aeb491718ea27596ab8bfc8bac3f9c5c201d5e66e2c2e2ead5d715262755d5b8a1aabaa6d5c4d121d4fc6e24a7aea60e7116327521f388394ba89f1c3e081d4136e1d232e9ed970da1274e7f386586ba6cd9c2f021d3286e15a0ae976f709e0274acc384780ba4f0dc20001d23ece0e202e902770620274725b82982ba31f1c11021d1552e06a1ae88d270261274389380b8cba1535c02081d06bedff252e818e6fea3273fd8b7ed9eb9f7b1bf3121cf844df7aaae7a566fae6273c44b7cfb8b9dae5be4201ce9f6df0322e733d6f72a2738bbb7b1dab9be7dbd5321cdbacde8bbae6bf46f36f27350cb79404b9a145bc6481cccf6de1472e64b46efb5273171377636b9845dbb7621cbe78dd9d4ae5d716ebfc2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page130Checked : PLift (fastPage primes 19 18 7254241 245824 940967 page130Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page130 (anchor : OMA.PrimePopulation.oddCount 7254241 = 940967) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page130Data i)) =
      rowCount (packedEvent page130Data i) := by
  exact fastPage_sound (width:=245824) (bound:=5000) (base:=7254241) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page130Checked.down

private theorem page130Good : GoodPage page130Data := by
  have anchor : oddCount 7254241 = 940967 := by exact page129Good 63 (by decide)
  exact (page130 anchor)

private def page131Data : ℕ := 0x7a2cdbb20b0bd0eedd8c801e83b2ec4542f400a76134279f143b01f2bcf12dd7d221e74ccebca5af389b75d5d279b5dbae33cbcd3b5d6dc81e6648eb4f92f313a759872797b3bac48ebcb661d5e721e579aead4eaf29f2755b22794173aa5e8bc999dd4f201e4918ea5a62f22ab751de2790653a874abc7bb9d3fd21e3a4ce9dffaf1b5274e0b278cb3ba68b4bc5e69d30881e2b7ce965b2f13ea74a39278908ba4a26bc40cdd21421e1cace8eb8af0c707466827854cba2ba0bc22d9d12001e0dbee87182f04f5742982781943a0d22bc0539d02c21dfee4e7f79aefdac73ec9277deeb9eeacbbe861cf3881df09ce77dd2ef65873afb277a3a39d03ebbca89ce4521de1b2e7042aeeefc7372e27769639b1d8bbad55cd5201dd2f4e68aa2ee7b3733622772ecb9937abb8fe5cc5f21dc462e6113aee06072f97276f43397524bb72f1cb6c81db5c0e597f2ed90472bcd276b9b3956d6bb5549ca7a21da6e4e51ecaed1ad728042

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page131Checked : PLift (fastPage primes 19 18 7500065 249920 970709 page131Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page131 (anchor : OMA.PrimePopulation.oddCount 7500065 = 970709) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page131Data i)) =
      rowCount (packedEvent page131Data i) := by
  exact fastPage_sound (width:=249920) (bound:=5000) (base:=7500065) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page131Checked.down

private theorem page131Good : GoodPage page131Data := by
  have anchor : oddCount 7500065 = 970709 := by exact page130Good 63 (by decide)
  exact (page131 anchor)

private def page132Data : ℕ := 0x7ded53d10d0beef65e84801f73def404c2fb80879f2c27db16bcf192bed129e74e21f64b6f387dafb07b79b4527d753bcd25cbeb355e65481f55d6f30b12fa8f57975f27d38bbcb32ebe94f5e55b21f46b0f28e6afa18e7937a27cfd7bc9408be76fde46201f37c2f211e2f99f678f9627cbfb3c74eabe5841e36921f2852f1957af924078bb327c831bc55d4be3a21e27081f194af11932f8acb787d127c4813c36c6be1c6de17821f0a98f09d0af8367783f027c0c4bc17c0bdfebde08001efb92f02102f7be87801027bd0d3bf8c2bde0f5df8821eecaeefa51af747477c3127b94f3bd9ccbdc305de9081eddd2ef2952f6d0e7785327b5913bbadebda4f9dd9921ecec8eeadaaf658d7747627b1d13b9bf8bd8755dca201ebfe6ee3222f5e0d7709a27ae1f3b7d1abd6919dbab21eb0deedb6baf569a76cbf27aa5f3b5e44bd4b35dab481ea1d4ed3b72f4f17768e527a6963b3f76bd2d41d9be21e92e0ecc04af47857650c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page132Checked : PLift (fastPage primes 19 18 7749985 254016 1000859 page132Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page132 (anchor : OMA.PrimePopulation.oddCount 7749985 = 1000859) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page132Data i)) =
      rowCount (packedEvent page132Data i) := by
  exact fastPage_sound (width:=254016) (bound:=5000) (base:=7749985) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page132Checked.down

private theorem page132Good : GoodPage page132Data := by
  have anchor : oddCount 7749985 = 1000859 := by exact page131Good 63 (by decide)
  exact (page132 anchor)

private def page133Data : ℕ := 0x81b7cbf08f0c0d435f8080206656fbe443031437de242817aa3ee932c0b561f70a22056dafb655b029827da2d2813c6bec97cc096c9f60c82047b2fae693021f67d637281006bea9cec07825f50f220383afa67eb01a407d242280c2a3e8a28c059b5f4120202906f9e9630129a7ce4e280857be6a8ac03b71f31522019d6f96afb00b147ca5b280499be4af4c01d75f2188200b1cf8ecb3003a97c6692800de3e2b66bfff31f11c21ffbc2f86e8affc0b7c27827fd0e3e0be0bfe0b9f02001fec94f7f082ff46d7be8827f93b3dec62bfc25def2421fdd6cf7729afecc67ba9927f5673dccecbfa38dee2881fcdf8f6f4d2fe51d7b6ab27f1a0bdad7ebf8589ed2d21fbf18f6772afddba7b2be27ede1bd8e18bf679dec3201faff2f5f9a2fd6157aed227ea1ebd6ebabf494deb3721fa0f8f57c3afcea47aae727e657bd4f64bf2acdea3c81f91b2f4fef2fc70f7a6fd27e2973d3016bf0d79e94221f82dcf481cafbf837a3142

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page133Checked : PLift (fastPage primes 19 18 8004001 258112 1031594 page133Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page133 (anchor : OMA.PrimePopulation.oddCount 8004001 = 1031594) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page133Data i)) =
      rowCount (packedEvent page133Data i) := by
  exact fastPage_sound (width:=258112) (bound:=5000) (base:=8004001) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page133Checked.down

private theorem page133Good : GoodPage page133Data := by
  have anchor : oddCount 8004001 = 1031594 := by exact page132Good 63 (by decide)
  exact (page133 anchor)

private def page134Data : ℕ := 0x85937410910c2c21608080215d3d03e3c30aca281e1c285557c0e8d2c2a2d607062214d890362db0a4c781a15285172c0c89cc283a206048213df502e21309d088160f284d7bc0a86ec263e205032212e1502616b095188120a284998408848c2452a04020211e9b01e0e308d5a80e062845bbc0682ac2266203012210f3f01607b085a980a032841e4c04814c2079a0200820ffeb00e03307e1980601283e17c02806c1e8b60100220f09f00600b0765780200283a2cc00800c1c9ba0000020e0f4ffe00306e947fe0028364d3fe802c1aaf5ff00220d18eff601b066cd7fa0128326f3fc80cc18bc9fe00820c206fee05305f2e7f603282e9e3fa81ec16d49fd01220b2d0fe60ab0577b7f206282acabf8838c14e7dfc02020a35afde12304fb97ee0a2826f73f685ac12fd5fb032209408fd61bb048137ea0f28230ebf4884c1108dfa048208474fce273040587e615281f37bf28b6c0f239f906220757cfc634b038c97e21c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page134Checked : PLift (fastPage primes 20 19 8262113 262208 1062649 page134Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page134 (anchor : OMA.PrimePopulation.oddCount 8262113 = 1062649) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page134Data i)) =
      rowCount (packedEvent page134Data i) := by
  exact fastPage_sound (width:=262208) (bound:=5000) (base:=8262113) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page134Checked.down

private theorem page134Good : GoodPage page134Data := by
  have anchor : oddCount 8262113 = 1062649 := by exact page133Good 63 (by decide)
  exact (page134 anchor)

private def page135Data : ℕ := 0x897c4431130c4b6521848022570f0c0343129a385f142893d042f072c496761742222475f0b805b121b585afd288fe6c2cfbcc4779e163c82237a50afd93119d1856e7288bed42af0ec457261537222278b0a7aeb111de852d22887fa428e68c437ce143202217fd09f86310a1284ebe288413c26dcac41876132d222081f0975fb1021a84aab288013c24d34c3f8aa1228821f88308f3b30fa5884699287c35c22ca6c3d9aa1124221e91508718b0f28284288287836c20c20c3b9f21020021d8fd07ef830ea7c83e7828744141eba2c39a3a0f1c221c945076d9b0e2a683a6928706341cb2cc37b660e18821b9af06ebd30dade8365b286c7041aabec35c0a0d15221aa31066a2b0d3238324e2868a1418a58c33d6a0c120219af305e8a30cb9382e422864d5c169fac31f060b0f2218ba905673b0c3e782a372860f74149a4c300060a0c8217c3504e5f30bc1e8262d285d1c412956c2e10e090a2216c950464cb0b446822242

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page135Checked : PLift (fastPage primes 20 19 8524321 266304 1094254 page135Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page135 (anchor : OMA.PrimePopulation.oddCount 8524321 = 1094254) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page135Data i)) =
      rowCount (packedEvent page135Data i) := by
  exact fastPage_sound (width:=266304) (bound:=5000) (base:=8524321) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page135Checked.down

private theorem page135Good : GoodPage page135Data := by
  have anchor : oddCount 8524321 = 1094254 := by exact page134Good 63 (by decide)
  exact (page135 anchor)

private def page136Data : ℕ := 0x8d6dec52150c6af2228c8023539f1442c31a7c18a10c28d2dac50012c68f6e27be22343bd13bddb1a00289ce528cef9c4dedcc66ff226b4823341f13391319812898bf28cb1144bdaec650aa25ab223247f12b46b1903e8949a28c724449c88c630fa24a2023147d122fe31882f8907628c314447b6ac610762399223040911ab7b1801188c5328bf04445a54c5f06e2290822f4611127331782d8883128bb1cc43946c5d1262188222e49910a30b1702e8841028b720c41840c5b1322080022d4c3101f031687087ff028b33cc3f742c592261f78222c51b0f9b1b1609c87bd128af40c3d64cc571de1e70822b4ff0f17531588b877b328ab4ec3b55ec552e21d69222a5950e93ab150d28739628a768c39478c533ca1c6202295eb0e1023148f286f7a28a37843739ac5140e1b5b222860f0d8cbb1412286b5f289fa2c352c4c4f5561a5482276970d09731394b86745289baa4331f6c4d572194e22266f90c864b131868632c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page136Checked : PLift (fastPage primes 20 19 8790625 270400 1126280 page136Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page136 (anchor : OMA.PrimePopulation.oddCount 8790625 = 1126280) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page136Data i)) =
      rowCount (packedEvent page136Data i) := by
  exact fastPage_sound (width:=270400) (bound:=5000) (base:=8790625) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page136Checked.down

private theorem page136Good : GoodPage page136Data := by
  have anchor : oddCount 8790625 = 1126280 := by exact page135Good 63 (by decide)
  exact (page136 anchor)

private def page137Data : ℕ := 0x9170a473970c8b022398802454011ca243227df8e4042912ee4717b2c88f5e387a22443931c1b5b21fc38dfcd290edf46f5fcc86efa376c824335b1b9493217a98db97290acac6d44ec84e76365f224231f1b0deb20f968d7622906c946b2a8c82e06355202413151a8763207898d32e2902ca46910ac80e56344522403311a00fb1ffa88cefb28fee1466f74c7eede3338823f389197ab31f7b28cac928fad3464de6c7cf0a322c223e37118f48b1efad8c69828f6cf462c60c7aeaa3120023d34d186e831e7af8c26828f2d4c60ae2c78f323014223c3a117e89b1dfd38be3928eeee45e96cc76f4a2f08823b3991762d31d7b78ba0b28eadec5c7fec74ef62dfd223a35d16dd2b1cfbd8b5de28e6d3c5a698c72ea62cf202393651657a31c78f8b1b228e2c245853ac70dde2be722382f315d23b1bf7e8ad8728debe4563e4c6ee722adc823733d154cf31b7a08a95d28dad5c54296c6cefe29d2223636d14c7cb1afbc8a5342

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page137Checked : PLift (fastPage primes 20 19 9061025 274496 1158589 page137Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page137 (anchor : OMA.PrimePopulation.oddCount 9061025 = 1158589) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page137Data i)) =
      rowCount (packedEvent page137Data i) := by
  exact fastPage_sound (width:=274496) (bound:=5000) (base:=9061025) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page137Checked.down

private theorem page137Good : GoodPage page137Data := by
  have anchor : oddCount 9061025 = 1158589 := by exact page136Good 63 (by decide)
  exact (page137 anchor)

private def page138Data : ℕ := 0x957ce495990cab64a4a8802557152521c32a9a1927fc2953c2c93752ca95e2497622546df2498db2a16c923b5294fb749151cca7566486482536952410132993991f6f294ba048f2eeca547a4753225264523876b2912991b2a29479448d0c8ca343e4642025160722fee328909916e629438648aeaaca1406453122505f322767b280d7912a3293f73c88c94c9f34e4420824f5b521ee33278da90e61293b5bc86a86c9d2d64310224e58721660b270b790a20293757484880c9b29a4200024d51920de0326870905e0293334482682c9919e40f0224c4d920561b2606e901a1292f3ec8048cc972063fe0824b4d71fce53258698fd63292b25c7e29ec951363ed1224a48f1f46ab2502f8f92629271e47c0b8c930ee3dc2024949b1ebf23248398f4ea292324479edac910ee3cb3224845b1e37bb240208f0af291f11477d04c8f00a3ba482473d31db073237f68ec75291af1c75b36c8cfc63a9622463cb1d294b2300b8e83c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page138Checked : PLift (fastPage primes 20 19 9335521 278592 1191444 page138Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page138 (anchor : OMA.PrimePopulation.oddCount 9335521 = 1191444) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page138Data i)) =
      rowCount (packedEvent page138Data i) := by
  exact fastPage_sound (width:=278592) (bound:=5000) (base:=9335521) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page138Checked.down

private theorem page138Good : GoodPage page138Data := by
  have anchor : oddCount 9335521 = 1191444 := by exact page137Good 63 (by decide)
  exact (page138 anchor)

private def page139Data : ℕ := 0x9999ccb81b0ccc42e5bc80265e112dc14332cf096cf429956dcb5ef2cca32a5ab22264d512d365b324949689d299147cb3c3ccc8232599c8263ce12cab9331c5696447298d1bcb198ecc60ba58872262c532c20eb3140995ff22988fe4af6e8cc400257720261bed2b966330be295b9e2984dfcad44acc1efe565d2260b3d2b0bfb303819574b2980bc4ab1b4cbfe1e5548825faeb2a81b32fb7b952f9297cbc4a8f26cbddc25434225eacd29f78b2f36594ea82978aa4a6ca0cbbd225320025da6f296d832eb4c94a58297496ca4a22cb9c92520c225ca4d28e39b2e31a946092970804a27accb7b9250f8825b9d12859d32dac8941bb296c544a053ecb5ac24fe5225a93327d02b2d27593d6e29683a49e2d8cb398a4ed2025987d2746a32ca439392229641ec9c07acb18da4dbf225883f26bd3b2c210934d7295ff7499e24caf7764cac82577c32633f32b9d39308d295be9c97bd6cad70a4b9a225676525aacb2b1a892c442

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page139Checked : PLift (fastPage primes 20 19 9614113 282688 1224604 page139Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page139 (anchor : OMA.PrimePopulation.oddCount 9614113 = 1224604) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page139Data i)) =
      rowCount (packedEvent page139Data i) := by
  exact fastPage_sound (width:=282688) (bound:=5000) (base:=9614113) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page139Checked.down

private theorem page139Good : GoodPage page139Data := by
  have anchor : oddCount 9614113 = 1224604 := by exact page138Good 63 (by decide)
  exact (page139 anchor)

private def page140Data : ℕ := 0x9dc3ecdb1d0ced94a6d48027686b3680c33b2129b2ec29d8054d8e92ceb82a6c2e22757d135f3db3a9c29ae8529d3d8cd6b5cce96b26b14827470f3567133a17e9aa1f29cfb0cd482ece753e69fb227367b34da6b399149a5ba29cb834d2508ce53e268e20272609344de3390e59a15629c770cd01eace331e67c9227153d33c17b3887999cf329c3334cded4ce110666b082704913335333802f9989129bf13ccbbc6cdf0926598226f40f32a90b377e99943029baeecc98c0cdceee6480026e345321d0336f9e98fd029b6c2cc75c2cdadb66368226d28531911b3672d98b7129b28dcc52cccd8c366250826c1e531055335ed79871329ae5fcc2fdecd6afe6139226b12b3079ab35686982b629aa38cc0cf8cd497e6022026a0772fee2334e1b97e5a29a6014bea1acd28565f0b2268fe12f62bb345e4979ff29a1eccbc744cd071e5df48267f552ed77333d91975a5299dc6cba476cce5c65cde2266edd2e4c4b335519714c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page140Checked : PLift (fastPage primes 20 19 9896801 286784 1258297 page140Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page140 (anchor : OMA.PrimePopulation.oddCount 9896801 = 1258297) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page140Data i)) =
      rowCount (packedEvent page140Data i) := by
  exact fastPage_sound (width:=286784) (bound:=5000) (base:=9896801) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page140Checked.down

private theorem page140Good : GoodPage page140Data := by
  have anchor : oddCount 9896801 = 1258297 := by exact page139Good 63 (by decide)
  exact (page140 anchor)

private def page141Data : ℕ := 0xa1fa04fe9f0d0f4c67f0802876313f6043438f69f9e42a1b67cfc632d0d3067dea22865553ed15b4308f9f56d2a17334fa27cd0b11e7ccc82854293e42934280a9f0f72a12e84f7eced08ef67baf22843593db3eb41fa09ec822a0ec5cf5b28d06dca7a92028328d3d2563417349e80e2a0a91cf378ad04c26797522821bd3c96fb40ecd9e39b2a065d4f13f4d02a52785882810f93c08b3406559df292a02144ef066d0080a773c227ff973b7a8b3fd939dab829fdc34ecce0cfe5727620027eec53aec833f5519d64829f98bcea962cfc4127504227ddf73a5e9b3ece39d1d929f557ce85eccfa28673e8827ccf539d0d33e45d9cd6b29f1204e627ecf808272cd227bc3739432b3dc0b9c8fe29ece94e3f18cf5ede71b2027ab3f38b5a33d37d9c49229e8bd4e1bbacf3d5670972279a8338283b3cb1f9c02729e484cdf864cf1c1a6f7c82789d3379af33c2e29bbbd29e06ccdd516cefb066e622277957370dcb3ba939b7542

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page141Checked : PLift (fastPage primes 20 19 10183585 290880 1292413 page141Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page141 (anchor : OMA.PrimePopulation.oddCount 10183585 = 1292413) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page141Data i)) =
      rowCount (packedEvent page141Data i) := by
  exact fastPage_sound (width:=290880) (bound:=5000) (base:=10183585) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page141Checked.down

private theorem page141Good : GoodPage page141Data := by
  have anchor : oddCount 10183585 = 1292413 := by exact page140Good 63 (by decide)
  exact (page141 anchor)

private def page142Data : ℕ := 0xa63e8d22a10d316a69108029871d485fc34c172a41dc2a5fb7d205d2d2f52a8fe6229765b47cedb4b8f8a3d552a5b6951e19cd2d24a8ec482964bf473e134b02da38cf2a570651bd6ed2afe28da3229539546ad6b4a7b4a344a2a52cb519948d28d928c820294277461ce349f0fa2fc62a4e7ad1752ad26b7a8b612293151458c7b49693a2b432a4a3ed15114d2494e8a40829206f44fc3348e12a26c12a45ef512d06d2269289202290eeb446c0b4853fa22402a4193d10900d2042e8800028fdd543dc0347cdaa1dc02a3d62d0e502d1e29a86e0228ecf9434c1b4746ca19412a391a50c10cd1c06685c0828dc3942bc5346bf6a14c32a34e6d09d1ed19ef684a1228cb03422cab4636ea10462a30a0d07938d17cf28382028ba47419d2345b10a0bca2a2c7450555ad15aee8263228a943410dbb45279a074f2a2833d03184d138e681448289813407e73449efa02d52a23e4d00db6d11646802622886f53fef4b441659fe5c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page142Checked : PLift (fastPage primes 20 19 10474465 294976 1326912 page142Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page142 (anchor : OMA.PrimePopulation.oddCount 10474465 = 1326912) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page142Data i)) =
      rowCount (packedEvent page142Data i) := by
  exact fastPage_sound (width:=294976) (bound:=5000) (base:=10474465) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page142Checked.down

private theorem page142Good : GoodPage page142Data := by
  have anchor : oddCount 10474465 = 1326912 := by exact page141Good 63 (by decide)
  exact (page142 anchor)

private def page143Data : ℕ := 0xaa926d47230d5407aa34802a9bed517f4354bc0a8ad42aa4d5d44d72d51e12a22222a8ad550ec5b54359a863d2aa09d5428bcd4fc92a0fc82a79b750599353aaca81a72a9c38d4040ed4d9129fd722a68214fc6eb531d8a7d122a97db53df68d4b63e9eb202a56d74f34635294fa787e2a939653bacad493b29d8d22a45414ea1fb52072a73eb2a8f1c539634d470229c6882a33e34e0fb3517c0a6f592a8ace5371a6d44d929b4422a22894d7d8b50f14a6ac82a8675534d20d42b329a2002a11194ceb8350667a66382a82285328a2d408a698fc229fff94c599b4fdc7a61a92a7dc953042cd3e60a97d8829ee9f4bc7d34f51da5d1b2a797bd2dfbed3c33296b5229dd4b4b362b4ec71a588e2a751fd2bb58d3a0929592029cbcf4aa4a34e3c7a54022a70cc5296fad37e1a946f229bad34a133b4db39a4f772a6c935272a4d35b82934c829a9874981f34d295a4aed2a682fd24e56d3391a922a229982f48f0cb4c9fca46642

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page143Checked : PLift (fastPage primes 20 19 10769441 299072 1361873 page143Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page143 (anchor : OMA.PrimePopulation.oddCount 10769441 = 1361873) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page143Data i)) =
      rowCount (packedEvent page143Data i) := by
  exact fastPage_sound (width:=299072) (bound:=5000) (base:=10769441) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page143Checked.down

private theorem page143Good : GoodPage page143Data := by
  have anchor : oddCount 10769441 = 1361873 := by exact page142Good 63 (by decide)
  exact (page143 anchor)

private def page144Data : ℕ := 0xaef0356c250d76f36b5c802bb3275abec35d768ad4cc2aea99d69d12d74bdeb49e22ba1555a29db5ce74ad0252ae624d677dcd72826b37482b8fb35995135c5c9acb7f2ae1d35652aed70546b24b22b7e4d59006b5bcf4ac6da2add62d62d88d6e20ab12202b6ccb586be35b41fac2362ad8f7d6086ad6bea6aff922b5aed57d77b5ab41abd932ad48555e354d69b62aed082b494d5743335a281ab8f12ad01cd5be46d67862ada822b37cb56af0b599b7ab4502acbc7559940d65592ac8002b2687561b0359112aafb02ac774d57442d632c2ab5822b151955871b58860aab112ac318554f4cd6103aaa3082b03bd54f35357fbdaa6732abed4552a5ed5ed7aa90922af25b545fab576f3aa1d62aba5fd50578d5caa6a7e202ae0e953cc2356e41a9d3a2ab60b54e09ad5a7baa6bb22acf995338bb565a2a989f2ab1c1d4bbc4d5855ea59482abe9752a57355d2ca94052aad7cd496f6d5631aa46e22aad3952124b5547ea8f6c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page144Checked : PLift (fastPage primes 20 19 11068513 303168 1397325 page144Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page144 (anchor : OMA.PrimePopulation.oddCount 11068513 = 1397325) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page144Data i)) =
      rowCount (packedEvent page144Data i) := by
  exact fastPage_sound (width:=303168) (bound:=5000) (base:=11068513) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page144Checked.down

private theorem page144Good : GoodPage page144Data := by
  have anchor : oddCount 11068513 = 1397325 := by exact page143Good 63 (by decide)
  exact (page144 anchor)

private def page145Data : ℕ := 0xb35e2591a70d9a5aec88802cce77641e4366513b1fc42b3168d8f4b2d98266c75a22cbc9963875b65c16b1b0d2b2cefd8cefcd95e26c62c82caa9562f09365308b16572b2868d8a94ed93a66c4ff22c98dd6259eb64a25b11a22b2405d883a8d91736c3d202c876961c3636418cb0cee2b1f9dd85e0ad8f3b6c2a522c7571612cfb6387ab083b2b1b21583874d8d08ec17882c63c16096b362facb03892b16c25812e6d8adaac04c22c524560008b626f4afed82b125ad7ed60d889febf2002c40995f6a8361e0dafa282b0de9d7c7e2d865e6bdf422c2e7b5ed49b61513af5792b0970d7a26cd8429abcc882c1cfd5e3ed360c48af0cb2b050a577cfed81f8abb9d22c0b555da92b6036caec1e2b009ed75798d7fbeaba7202bf9935d13a35fa97ae7722afc3057323ad7d89eb94722be7a55c7e3b5f19dae2c72af7ba570ce4d7b51ab81c82bd6295be8f35e8f5ade1d2af365d6e796d7925ab6f222bc4e15b53cb5e038ad9742

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page145Checked : PLift (fastPage primes 20 19 11371681 307264 1433094 page145Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page145 (anchor : OMA.PrimePopulation.oddCount 11371681 = 1433094) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page145Data i)) =
      rowCount (packedEvent page145Data i) := by
  exact fastPage_sound (width:=307264) (bound:=5000) (base:=11371681) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page145Checked.down

private theorem page145Good : GoodPage page145Data := by
  have anchor : oddCount 11371681 = 1433094 := by exact page144Good 63 (by decide)
  exact (page145 anchor)

private def page146Data : ℕ := 0xb7d535b7a90dbe1a2db8802dec5b6d9dc36f401b6bbc2b78e45b5452dbbe1ada5622dda816d04db6eb08b66f52b7454db2e1cdb999ed92482dc82d6c6c136e1e0b622f2b6fca5b07eedb7562d7f322db66b6bd36b6d8fab5d6a2b6b6ddae1c8db520ad6c202da48f6b3ae36d008b58a62b66eedabbaadb2e46d59122d92a16aa27b6c712b53e32b62695a9594db0a56d46082d80cb6a0a336be2cb4f212b5e01da6f86dae71ad33022d6f1569720b6b559b4a602b598a5a4980dac306d20002d5cfb68da036ac4ab45a02b550e5a2382da9f46d0d022d4b2568421b6a360b40e12b508359fd8cda7bcacfa082d396567aa5369a74b3c232b4c2259d79eda581ece7122d277b6712ab69174b37662b47a159b1b8da3436cd4202d15a5667b23688b0b32aa2b4337598bdada1086cc1322d03af65e3bb67fa8b2def2b3eadd96604d9ec9ecae482cf1d7654c73676b3b29352b3a43594036d9c986c9b622ce08d64b54b66dfab247c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page146Checked : PLift (fastPage primes 20 19 11678945 311360 1469380 page146Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page146 (anchor : OMA.PrimePopulation.oddCount 11678945 = 1469380) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page146Data i)) =
      rowCount (packedEvent page146Data i) := by
  exact fastPage_sound (width:=311360) (bound:=5000) (base:=11678945) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page146Checked.down

private theorem page146Good : GoodPage page146Data := by
  have anchor : oddCount 11678945 = 1469380 := by exact page145Good 63 (by decide)
  exact (page146 anchor)

private def page147Data : ℕ := 0xbc5e6dde2b0de265aeec802f0ea1773d4378518bb8b42bc1625dbbf2de020aed9222efc9d76a25b77bf4bb3dd2bbcd65d953cdddd7aec5c82eea47760793772d3baf072bb8485d6e8eddb8feeb2722ed7d3756ceb769adbaa322bb3c1dd47e8dd9526e9f202ec62174d263760ccba55e2baf445d214add70fee8bd22eb3e77437fb757a8ba08b2baaafdcfab4dd4c86e78882ea1ab739db374e8cb9bb92ba6255cd426dd281ae65422e8f9b73038b74584b96e82ba19cdcada0dd03d6e52002e7d2372698373c4cb92182b9d0cdc8722dcdf2ee3ec22e6b1b71cf9b73334b8d492b9874dc60acdcba8ee2b882e58e57135d372a27b887b2b93ecdc3a3edc96bee18522e46b1709c2b72102b83ae2b8f5d5c13d8dc718ae05202e34997002a3717fdb7ee22b8adf5bed7adc4e7edf1f22e22c36f693b70f16b7a172b866adbc724dc2a0eddec82e109b6ecff370602b754d2b81e35ba0d6dc064edcba22dfe776e36cb6fcecb70842

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page147Checked : PLift (fastPage primes 20 19 11990305 315456 1505958 page147Data 64) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page147 (anchor : OMA.PrimePopulation.oddCount 11990305 = 1505958) :
    ∀ i < 64, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page147Data i)) =
      rowCount (packedEvent page147Data i) := by
  exact fastPage_sound (width:=315456) (bound:=5000) (base:=11990305) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page147Checked.down

private theorem page147Good : GoodPage page147Data := by
  have anchor : oddCount 11990305 = 1505958 := by exact page146Good 63 (by decide)
  exact (page147 anchor)

private def page148Data : ℕ := 0x5f939afaf082fc5577d51337e079be9512bef08df40c6df6eeaf9b822fb2c17cb50b7d727be4702bea71df19c0df4a36f88002fa0d57c19037ce20bdf902be5ec5ef2c2df2662f74822f8e897b7d1b7c502bdab12be14b5ecbccdf0186f61082f7c3f7ae1537bbeebd5d32bdcd2dea4dededd86f4d922f6a4d7a45ab7b2dfbd0f62bd83fde7df8deb8a6f3a202f57e379aa237a9a0bcc1a2bd3bbde571ade946ef26b22f45a9790ebb7a081bc73f2bcf215e3044de6f66f13482f33057873737972abc2652bca6d5e0976de4a86effe22f20e577d84b78e0ebbd8c2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def page148Checked : PLift (fastPage primes 19 18 12305761 194239 1543117 page148Data 39) :=
  ⟨by
    unfold fastPage
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private theorem page148 (anchor : OMA.PrimePopulation.oddCount 12305761 = 1543117) :
    ∀ i < 39, OMA.PrimePopulation.oddCount (rowSlot (packedEvent page148Data i)) =
      rowCount (packedEvent page148Data i) := by
  exact fastPage_sound (width:=194239) (bound:=5000) (base:=12305761) roster_prime roster_complete
    (by decide) (by decide) (by decide) (by decide) anchor page148Checked.down

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem page148Good : GoodPage page148Data := by
  have anchor : oddCount 12305761 = 1543117 := by exact page147Good 63 (by decide)
  exact padded_page (by decide +kernel) (page148 anchor)

private theorem empty_pages : ∀ q ∈ ([] : List ℕ), GoodPage q := by simp

private theorem append_good_pages {a b : List ℕ} (left : ∀ q ∈ a, GoodPage q)
    (right : ∀ q ∈ b, GoodPage q) : ∀ q ∈ a++b, GoodPage q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact left q h
  · exact right q h

private def pages0 : List ℕ := (page0Data :: (page1Data :: (page2Data :: (page3Data :: (page4Data :: (page5Data :: (page6Data :: (page7Data :: (page8Data :: (page9Data :: (page10Data :: (page11Data :: (page12Data :: (page13Data :: (page14Data :: (page15Data :: []))))))))))))))))

private theorem pages0Good : ∀ q ∈ pages0, GoodPage q := (cons_good_page page0Good (cons_good_page page1Good (cons_good_page page2Good (cons_good_page page3Good (cons_good_page page4Good (cons_good_page page5Good (cons_good_page page6Good (cons_good_page page7Good (cons_good_page page8Good (cons_good_page page9Good (cons_good_page page10Good (cons_good_page page11Good (cons_good_page page12Good (cons_good_page page13Good (cons_good_page page14Good (cons_good_page page15Good empty_pages))))))))))))))))

private def pages1 : List ℕ := (page16Data :: (page17Data :: (page18Data :: (page19Data :: (page20Data :: (page21Data :: (page22Data :: (page23Data :: (page24Data :: (page25Data :: (page26Data :: (page27Data :: (page28Data :: (page29Data :: (page30Data :: (page31Data :: []))))))))))))))))

private theorem pages1Good : ∀ q ∈ pages1, GoodPage q := (cons_good_page page16Good (cons_good_page page17Good (cons_good_page page18Good (cons_good_page page19Good (cons_good_page page20Good (cons_good_page page21Good (cons_good_page page22Good (cons_good_page page23Good (cons_good_page page24Good (cons_good_page page25Good (cons_good_page page26Good (cons_good_page page27Good (cons_good_page page28Good (cons_good_page page29Good (cons_good_page page30Good (cons_good_page page31Good empty_pages))))))))))))))))

private def pages2 : List ℕ := (page32Data :: (page33Data :: (page34Data :: (page35Data :: (page36Data :: (page37Data :: (page38Data :: (page39Data :: (page40Data :: (page41Data :: (page42Data :: (page43Data :: (page44Data :: (page45Data :: (page46Data :: (page47Data :: []))))))))))))))))

private theorem pages2Good : ∀ q ∈ pages2, GoodPage q := (cons_good_page page32Good (cons_good_page page33Good (cons_good_page page34Good (cons_good_page page35Good (cons_good_page page36Good (cons_good_page page37Good (cons_good_page page38Good (cons_good_page page39Good (cons_good_page page40Good (cons_good_page page41Good (cons_good_page page42Good (cons_good_page page43Good (cons_good_page page44Good (cons_good_page page45Good (cons_good_page page46Good (cons_good_page page47Good empty_pages))))))))))))))))

private def pages3 : List ℕ := (page48Data :: (page49Data :: (page50Data :: (page51Data :: (page52Data :: (page53Data :: (page54Data :: (page55Data :: (page56Data :: (page57Data :: (page58Data :: (page59Data :: (page60Data :: (page61Data :: (page62Data :: (page63Data :: []))))))))))))))))

private theorem pages3Good : ∀ q ∈ pages3, GoodPage q := (cons_good_page page48Good (cons_good_page page49Good (cons_good_page page50Good (cons_good_page page51Good (cons_good_page page52Good (cons_good_page page53Good (cons_good_page page54Good (cons_good_page page55Good (cons_good_page page56Good (cons_good_page page57Good (cons_good_page page58Good (cons_good_page page59Good (cons_good_page page60Good (cons_good_page page61Good (cons_good_page page62Good (cons_good_page page63Good empty_pages))))))))))))))))

private def pages4 : List ℕ := (page64Data :: (page65Data :: (page66Data :: (page67Data :: (page68Data :: (page69Data :: (page70Data :: (page71Data :: (page72Data :: (page73Data :: (page74Data :: (page75Data :: (page76Data :: (page77Data :: (page78Data :: (page79Data :: []))))))))))))))))

private theorem pages4Good : ∀ q ∈ pages4, GoodPage q := (cons_good_page page64Good (cons_good_page page65Good (cons_good_page page66Good (cons_good_page page67Good (cons_good_page page68Good (cons_good_page page69Good (cons_good_page page70Good (cons_good_page page71Good (cons_good_page page72Good (cons_good_page page73Good (cons_good_page page74Good (cons_good_page page75Good (cons_good_page page76Good (cons_good_page page77Good (cons_good_page page78Good (cons_good_page page79Good empty_pages))))))))))))))))

private def pages5 : List ℕ := (page80Data :: (page81Data :: (page82Data :: (page83Data :: (page84Data :: (page85Data :: (page86Data :: (page87Data :: (page88Data :: (page89Data :: (page90Data :: (page91Data :: (page92Data :: (page93Data :: (page94Data :: (page95Data :: []))))))))))))))))

private theorem pages5Good : ∀ q ∈ pages5, GoodPage q := (cons_good_page page80Good (cons_good_page page81Good (cons_good_page page82Good (cons_good_page page83Good (cons_good_page page84Good (cons_good_page page85Good (cons_good_page page86Good (cons_good_page page87Good (cons_good_page page88Good (cons_good_page page89Good (cons_good_page page90Good (cons_good_page page91Good (cons_good_page page92Good (cons_good_page page93Good (cons_good_page page94Good (cons_good_page page95Good empty_pages))))))))))))))))

private def pages6 : List ℕ := (page96Data :: (page97Data :: (page98Data :: (page99Data :: (page100Data :: (page101Data :: (page102Data :: (page103Data :: (page104Data :: (page105Data :: (page106Data :: (page107Data :: (page108Data :: (page109Data :: (page110Data :: (page111Data :: []))))))))))))))))

private theorem pages6Good : ∀ q ∈ pages6, GoodPage q := (cons_good_page page96Good (cons_good_page page97Good (cons_good_page page98Good (cons_good_page page99Good (cons_good_page page100Good (cons_good_page page101Good (cons_good_page page102Good (cons_good_page page103Good (cons_good_page page104Good (cons_good_page page105Good (cons_good_page page106Good (cons_good_page page107Good (cons_good_page page108Good (cons_good_page page109Good (cons_good_page page110Good (cons_good_page page111Good empty_pages))))))))))))))))

private def pages7 : List ℕ := (page112Data :: (page113Data :: (page114Data :: (page115Data :: (page116Data :: (page117Data :: (page118Data :: (page119Data :: (page120Data :: (page121Data :: (page122Data :: (page123Data :: (page124Data :: (page125Data :: (page126Data :: (page127Data :: []))))))))))))))))

private theorem pages7Good : ∀ q ∈ pages7, GoodPage q := (cons_good_page page112Good (cons_good_page page113Good (cons_good_page page114Good (cons_good_page page115Good (cons_good_page page116Good (cons_good_page page117Good (cons_good_page page118Good (cons_good_page page119Good (cons_good_page page120Good (cons_good_page page121Good (cons_good_page page122Good (cons_good_page page123Good (cons_good_page page124Good (cons_good_page page125Good (cons_good_page page126Good (cons_good_page page127Good empty_pages))))))))))))))))

private def pages8 : List ℕ := (page128Data :: (page129Data :: (page130Data :: (page131Data :: (page132Data :: (page133Data :: (page134Data :: (page135Data :: (page136Data :: (page137Data :: (page138Data :: (page139Data :: (page140Data :: (page141Data :: (page142Data :: (page143Data :: []))))))))))))))))

private theorem pages8Good : ∀ q ∈ pages8, GoodPage q := (cons_good_page page128Good (cons_good_page page129Good (cons_good_page page130Good (cons_good_page page131Good (cons_good_page page132Good (cons_good_page page133Good (cons_good_page page134Good (cons_good_page page135Good (cons_good_page page136Good (cons_good_page page137Good (cons_good_page page138Good (cons_good_page page139Good (cons_good_page page140Good (cons_good_page page141Good (cons_good_page page142Good (cons_good_page page143Good empty_pages))))))))))))))))

private def pages9 : List ℕ := (page144Data :: (page145Data :: (page146Data :: (page147Data :: (page148Data :: [])))))

private theorem pages9Good : ∀ q ∈ pages9, GoodPage q := (cons_good_page page144Good (cons_good_page page145Good (cons_good_page page146Good (cons_good_page page147Good (cons_good_page page148Good empty_pages)))))

private def allPages : List ℕ := (pages0 ++ (pages1 ++ (pages2 ++ (pages3 ++ (pages4 ++ (pages5 ++ (pages6 ++ (pages7 ++ (pages8 ++ pages9)))))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem allPagesGood : ∀ q ∈ allPages, GoodPage q := (append_good_pages pages0Good (append_good_pages pages1Good (append_good_pages pages2Good (append_good_pages pages3Good (append_good_pages pages4Good (append_good_pages pages5Good (append_good_pages pages6Good (append_good_pages pages7Good (append_good_pages pages8Good pages9Good)))))))))

private def coversHeads (P : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, width+1 => decide (a.gcd P ≠ 1) && coversHeads P (a+1) width

private theorem coversHeads_sound (P a width : ℕ) (h : coversHeads P a width = true) :
    ∀ d, a ≤ d → d < a+width → d.gcd P ≠ 1 := by
  induction width generalizing a with
  | zero => omega
  | succ width ih =>
    change (decide (a.gcd P ≠ 1) && coversHeads P (a+1) width) = true at h
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
    intro d lo hi
    by_cases heq : d = a
    · exact heq ▸ h.1
    · exact ih (a+1) h.2 d (by omega) (by omega)

private theorem coversJoin {P a b c : ℕ}
    (left : ∀ d, a ≤ d → d < b → d.gcd P ≠ 1)
    (right : ∀ d, b ≤ d → d < c → d.gcd P ≠ 1) :
    ∀ d, a ≤ d → d < c → d.gcd P ≠ 1 := by
  intro d lo hi
  by_cases hm : d < b
  · exact left d lo hm
  · exact right d (by omega) hi

private theorem prime_of_covers {P b n : ℕ}
    (hcover : ∀ d, 2 ≤ d → d < b+1 → d.gcd P ≠ 1)
    (hn : 2 ≤ n) (hb : n < (b+1)^2) (hcop : n.gcd P = 1) : n.Prime := by
  by_contra h
  let d := n.minFac
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hsq : d^2 ≤ n := Nat.minFac_sq_le_self (by omega) h
  have hbound : d < b+1 := by
    by_contra! hbad
    have hh : (b+1)^2 ≤ d^2 := Nat.pow_le_pow_left hbad 2
    omega
  have hdiv : d ∣ P := by
    by_contra hnd
    exact hcover d hd.two_le hbound (hd.coprime_iff_not_dvd.mpr hnd)
  have hdg := Nat.dvd_gcd (Nat.minFac_dvd n) hdiv
  rw [hcop] at hdg
  exact hd.ne_one (Nat.dvd_one.mp hdg)

private def productSmall : ℕ := 0x18d63744d1e73fe25366

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def SmallFrom2Checked : PLift (coversHeads productSmall 2 62 = true) :=
  ⟨by decide +kernel⟩

private theorem SmallFrom2 : ∀ d, 2 ≤ d → d < 64 → d.gcd productSmall ≠ 1 :=
  coversHeads_sound productSmall 2 62 SmallFrom2Checked.down

private theorem coversSmall : ∀ d, 2 ≤ d → d < 64 → d.gcd productSmall ≠ 1 :=
  SmallFrom2

private def productLarge : ℕ := 0x12a8b71fd1159aa6da82d6eb04ecc97fb213a2938812ee1275934175750dea6b4b8984e7447d9763493e8bf845102561b79f0aa792786cde7d49daa53232922df8e7e01b2549666839b0b885ab1c07b9ddda7d0be6f71689c1e8fa69cc4af7f01281e0839c3b872e03d332671957738e08a62c565c1c11881d9f347a50c8d5c09277b09959cc7d434894e3b5a40ca7d1c3ab476f6cdc3f217fcde86fd814780f853fdb382cf5892dde9a23791a2487f42d757757616f353278e1b4992da9db3bde0d045a41d1f243167868751442111fd5d7c27a1d22a773e1d3a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def LargeFrom2Checked : PLift (coversHeads productLarge 2 256 = true) :=
  ⟨by decide +kernel⟩

private theorem LargeFrom2 : ∀ d, 2 ≤ d → d < 258 → d.gcd productLarge ≠ 1 :=
  coversHeads_sound productLarge 2 256 LargeFrom2Checked.down

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def LargeFrom258Checked : PLift (coversHeads productLarge 258 256 = true) :=
  ⟨by decide +kernel⟩

private theorem LargeFrom258 : ∀ d, 258 ≤ d → d < 514 → d.gcd productLarge ≠ 1 :=
  coversHeads_sound productLarge 258 256 LargeFrom258Checked.down

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def LargeFrom514Checked : PLift (coversHeads productLarge 514 256 = true) :=
  ⟨by decide +kernel⟩

private theorem LargeFrom514 : ∀ d, 514 ≤ d → d < 770 → d.gcd productLarge ≠ 1 :=
  coversHeads_sound productLarge 514 256 LargeFrom514Checked.down

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def LargeFrom770Checked : PLift (coversHeads productLarge 770 256 = true) :=
  ⟨by decide +kernel⟩

private theorem LargeFrom770 : ∀ d, 770 ≤ d → d < 1026 → d.gcd productLarge ≠ 1 :=
  coversHeads_sound productLarge 770 256 LargeFrom770Checked.down

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def LargeFrom1026Checked : PLift (coversHeads productLarge 1026 231 = true) :=
  ⟨by decide +kernel⟩

private theorem LargeFrom1026 : ∀ d, 1026 ≤ d → d < 1257 → d.gcd productLarge ≠ 1 :=
  coversHeads_sound productLarge 1026 231 LargeFrom1026Checked.down

private theorem coversLarge : ∀ d, 2 ≤ d → d < 1257 → d.gcd productLarge ≠ 1 :=
  (coversJoin (coversJoin LargeFrom2 LargeFrom258) (coversJoin LargeFrom514 (coversJoin LargeFrom770 LargeFrom1026)))

private def fastPrime (p : ℕ) : Bool :=
  if p ≤ 63 then decide p.Prime
  else if p < 64^2 then decide (p.gcd productSmall = 1)
  else decide (p < 1257^2 ∧ p.gcd productLarge = 1)

private theorem fastPrime_sound (p : ℕ) (h : fastPrime p = true) : p.Prime := by
  unfold fastPrime at h
  split at h
  · exact of_decide_eq_true h
  · split at h
    · exact prime_of_covers coversSmall (by omega) (by assumption) (of_decide_eq_true h)
    · have h' := of_decide_eq_true h
      exact prime_of_covers coversLarge (by omega) h'.1 h'.2

private def witness2Data : ℕ := 0x52414810134817040459012100a71fdc281763f206038c7d0100428f6c100cf1e88381ec3cb09011c785040500ec8140271d38084c839a9a01f472c0803e0e2a100261c04080883758200946dc020120d92040421ac810154352060100693040670cfc2007519a02007c32b820088645020650c5a2008b1844281122fc8500805e4020358bac1005417041803e2d90104dc5a11e05e0b0e2001e15c8081ae2b00a00e85480401c8a66080d3147c5006e2818202304e80c06809a0280a112d4380962500300d44880403888da1406f11742810222706025c43d0e0bb0858580331070101c22038d01103f60600c87c0040c40f24581e81da8f00603a30202f870e141010dcc880ba1ad85016c3450a027866c100590c68282441801501282ea0804b85a8240140af40804e1510202f42911a02905021401309ac0806a12e0302102481201184620804f088c2806610703012c2000a04283dc280480784281360e80c00b41be0600e03540802b0668180d40c40901f41781604802cc3400f05500801c0a18100681340400c82420802e044c2006c0818500300f90203101da2c01503841001606b8100c40d10a02c018a2c00a02e80806805806016c0a81a004013e0400802540802e04383004007b0400780e20800601900803a02d05001405502002009e0400401180802601e0400240360400c80601800700a01002801086004801b0c002002c0800a00442000400681000800902000800804001000c0800000081

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2Checked : PLift (checkWitnesses allPages fastPrime 2 witness2Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2 : ∀ n, 2 ≤ n → n < 127 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2Checked.down

private def witness127Data : ℕ := 0x9c7ad0106e0f53100a61e9a180be3d101809879f810450f390a0449e5c0848e3c94d81ca7910402e0f1a060711e22102d43c047809277a8102dceef060d21dc0202223b54581047650204e8ebe0c0b71d5e1c0d93a8c2075c74c950a30e8c1c0401cfe080b239cc18aca734a402c4e5d060981ca21807c39241008a71f0104a8e2a0c0949c3a18276383470708703150930df51a0219bcc0407937581056a6e5100108dc0020a59b681c0aa36b8180826d101046cd930c0bb1b0a2034335e4a03d46b70b00fcd5c0201f9a940403e34e4080e66968201c8d1d0409d9a1a1c3603404b00e0677820bc8ce02601e99ac042193330683ea65d8c0284cad06118193c3822e32347034e63e0a0300c6d0810398be340dc3138281fa6218601a0c350401d984604066304c103786048b06e4bfa1603217c8080632f6c103e65e88d02d8bc40806a176c140622e9c100c25ca8200e0b820209b16e22008f2d8c181645a90404ccb4110098965c200d02c78280bc586820dc4afd360c915d42c1712b6c501cc565860884ac12001a9568040852a94182c65480a0374a800c04194d60c2952970a8068526010160a3704061143c140c02818280fc4fb8300cc9dd0207913a61c0d526fc300644d68106149a1180189322041212600481d24b407014c9560401792920405224d4100ec4910303e8907100b911ec302502380a81ee4668804b88be14016115a040c72270301b04438706b486e1e03690b60c0d6210c3805441b81

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness127Checked : PLift (checkWitnesses allPages fastPrime 127 witness127Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness127 : ∀ n, 127 ≤ n → n < 252 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness127Checked.down

private def witness252Data : ℕ := 0x29e9350403f92640607ea4be0c069496c08a7292b950db125518033a4a6044ca493c983c0926860b7924a140a3a48c10193490c280ca91f0103e523b062182470404e748cca04ae91788095922b1012a244e2018e488c287889108e0f0121e1c05a24340813d485420494908081a1520b3e09c240e10204480c380c09000109fd1fa1207823ea0c33c47cc609648f89408fd1ed1038023ce9023847884046a8ee0804c91d508098a3a6105e9473ce0b4c8e69a11ad1c9260dd23841805e4704087848de0f1afd1b7460932366100e746b4180b88d50106bd1a50c188a3383016c46502815a8c7820c1d18c182e0230e7034445f86889a8bc9302ad1740414522d8280df458c186ca8af8e0ae915a16108a2aa20119453c2048e8a489045d143081c6a2783c2e644d4600b089701016112602053223a0826f4448505ba8878c054d1090a0a8a2061415044002814887e8207f90f710051a1dc0822b43a04820e86f04015d0d80208321a21035f4328780ac8620101590c2020c12170183b842c488d168562611210a42a02a213c0409e4268100a684a010c6108c1c09e2106141b141d83882e83414084505e121e3a0b4481e34144402ea82506014503f0204ca0740846240c8b858a8168d0141021023cca036d032b403c785168058c0bb10011c15c9fee342e73fa4702c27ee86024cfd7040631f960c4283f04b01867db8303bcfad082621f4a6c08e3e74103dc7c9890710f8b100e09ef4200c03db8182367b285

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness252Checked : PLift (checkWitnesses allPages fastPrime 252 witness252Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness252 : ∀ n, 252 ≤ n → n < 377 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness252Checked.down

private def witness377Data : ℕ := 0xe269bd99132537a1c263a6f2383714ddc48a1a9ba8f11d93741a045a6e6042b94dc8381149b8810ee536e14326a6da540894db0087669b58a119d36a1a04426d2041454da0181c89b28209693630c15326c21c3ab4d7c5010c9af010ea135d140a126b80c2a04d6c384a69ad0610953581809fa6ae0c4d84d54785e89a988194d3522c0fc26a0142964d3838a2a9a690036934b04040a694046c64d24c8dd49a39a03653460423da688384bc4d0c789fe9a01011d133d1c120a678182404cec30cbe99c9701fd336023c0266a7846a4cc470666997891dd532d3c0f42658141304ca41850499407035932704140264a1c27e4c8c383169908408a531e0c1142638182264c60304f098b0707793150a2d62624503ec4c40603b6987851b51309361f3a610305394c1c900f49830110693041a0eaa606140d24c041043a97f06104d2fc1a03c25f4042ae4bd440c1a9791717812f02c27325dc4411c4ba4181a29728209852e30e03ba5c2040764b7c0841e96c86072d2d50a08c25a40c37b4b3858e98965a005d12ca0808aa58a0c2554b043876c9600c01d12be023052578601c04ae82840695b060fad2b31a086a5640c1bb4ac028aa29571403292ab04064a554080704aa00819095382031d2a4040d9a53e1406e4a7408b8694d9708fd2970e1882528282394a4838920947910c2528c140ad25161006c4a1c082b09428410a92821e0aba502100c149f0105f693d0a07ad2770c0a9a4e21074f49bd1844893607

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness377Checked : PLift (checkWitnesses allPages fastPrime 377 witness377Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness377 : ∀ n, 377 ≤ n → n < 502 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness377Checked.down

private def witness502Data : ℕ := 0x150a06811fa940c301e3281620118502810338a048315714081a08b280e083bd501441280a02200821403080cca8040c4525004504e6a00050d393ff0e08927fc0844f4ff4502209fe021a393fb24052a7f4045434fe46875a9fc080b693f70c24b27ec2c6b34fd498f7a9fa180b553f30c16a27e2185f44fc0802169f78204293ee0422227da287404fb0b111c9f59d09953ea0a083a7d20818a4fa018cd29f39202893e602130a7ca144cf4f90608669f18a06193e20623927c22c4704f7c581429ef0104113dd0405027b8046594f6c90abe9ed0e14513d91a15c27b0184294f5c502049ea8229393d4542cb27a63c2b24f483013c9e88120b13d03822f279e2c0ff4f381013a9e6810aa53cc0c0f42796103164f2438eda9e4180f2d3c712229a78c2c2464f14281f89e20202713c3021b5a784205764f04791129e01f0c153be0e1dfa77a2440c4ef0501349dd010a613b90c35b2770544894edc602e09db0308dd3b50a2692768342344ecc283ae9d90402613b1023cca7606859f4ebc806a29d68829c53ab5c145a754180964ea4087ee9d40a17dd3a724336a74c501d14e94201ea9d2020fc53a31404a2742048024e7ce8b029cf10073139c080af27360c0924e64081e49cc020245397024c2272ca00f04e5410ca49ca140e393921213ca7201849b4e38681dc9c602107938b1619b27142008d4e2408ba29c4120231387021bfa70c247fe4e14f01d69c18216613822228f27023c7784e00d84209be05

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness502Checked : PLift (checkWitnesses allPages fastPrime 502 witness502Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness502 : ∀ n, 502 ≤ n → n < 627 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness502Checked.down

private def witness627Data : ℕ := 0x3cea4683181d48c1a176a91614267522820dbea44900dc14880c34e290e3c49b521848d30a428f16dd48418132290610db05209e86d4a408610e9480101b228fe1849251f848292a3e82077d47c064a128f66c5ee51e868b54a3c8c0771478063c928ee4c0b951d8083b4a3a8309694740816ca8e61454c51c8584b2a388410b14701059e28dea047a51b848c70a368e18cd46c1c16928d61425451a820ce8a348f050146804166a8ce1472f51989016ca32811ba14642205aa8c60458c518860778a30870eed4600e23428be241cf517819154a2e991b7945c2220ca8b6205ca516868580a2c851a6d458202bca8ae302445158214b6a2aa31e51454281a128a618b89514960f8ca289516ed4501a059a89e04571513860816a268817e544c1c20428962023b51282108aa24980715448063bea88e504aa511850468a2284070944406058a884042a5510428548a2005203d43f2e097a87c080af50f40893ca1e0a155543b1827e28722c83150e0c0646a1b86168d4361a3aa286a5062750d0789eca198b04a143204093a862081b450c018a8aa178c165142e1a0d9285a0c1b150b01890ea158a0fa142a10307a8523c12350a01015ca13810f91426101bca84a1c1ab5090190cea119a11dd4221409028420864b508080fbca0f971dad41e2a215a83a240ac507008998a0d8b02ad41a022b92832342fc5060308d2a0b8a1c8d415281b4a8281c56d504c68152a090118ed411201b128201c5e6503c78234a0702

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness627Checked : PLift (checkWitnesses allPages fastPrime 627 witness627Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness627 : ∀ n, 627 ≤ n → n < 752 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness627Checked.down

private def witness752Data : ℕ := 0x103ca851214fd5091254baa1074742541c78beca830b14ed505121f3aa0818a8d540ce8982a810812f5501103772a003818053fc10972a7f080add4fd0825ba9f82097a53ecc06a0a7d051b914f91c32529f0303d853dc30bcaa7b0b14b94f51210da9e80c69653cc68b22a790a0d2d4f10a41ca9e04c2aa53bc2087ca770705f14ed0468a29d8c058453ac50bb8a750b0f314e90c0bca9d00857f539c50feca731208514e50624ea9c82075e538c812a4a711817494e1161e3a9c01829c537c2019ca6f0117314dd166f6a9b8e433e536c28416a6d0312454d91014ca9b01061f535c60412a6b03224d4d52a33929a834814534c9911aa691523054d12c39fa9a0400cd533c0965aa67230ecd4cd0c1d8a99818b00532d10b72a650b05ad4c904147a990104f2531c4865aa630503314c5020b4a98808328530c28196a610113a54c1123bf29804491952fcc0ef6a5f1133794bd620b2a978087b152ec90748a5d061dc54b9220fea9700c1fc52dc189baa5b0905814b5041422968103a052cc309aca59090e794b10c29ea96028af652bd183eca570316794ad16388a958400c452ac088b8a550807d14a90613da95010be0529d5098ca53091f614a52631b294834304528c282b2a510219ed4a11c297a940281f0527c185fea4f0521b149d2c0aba93808626526c682aaa4d020bf14990a0f6a9300c787525c903d6a4b030ded4950c3dba9284c152524c11052a4915054549104134a920103ef523c3817ea4701

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness752Checked : PLift (checkWitnesses allPages fastPrime 752 witness752Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness752 : ∀ n, 752 ≤ n → n < 877 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness752Checked.down

private def witness877Data : ℕ := 0x648ac38413255860e1342b0a0c901561098dc0ac18c0f095820a0db2b02083c0560028886abf861b7557e1818caafa100e855f008c38abd8a209157a20131aaf20ca3255e0c0d02abb8b06c557604595aaea7443955d03035eab9822171572221da2ae2146d155c061706ab79f370d56e5e33a2ada2c53555b040b50ab589375956a60363aad23084a55a088d86ab38c26815662c252aaca1c303559020f82ab18f199d562164052ac240840558088600aaf84038155e022d02aba248055570818eeaada60e9955a0a0d3aab20890d5560a034caab82037d556023572aaa307aa5550781bcaa9810691552040d1aaa2087f85540810f2aa792068154e0454eaa9a6c589553049360aa597289d54a3262f2a929819e5520101b6aa3811609546122c0aa8a244185510305d6aa18412095420e4312a82485de550050828a9f860e2d53e0a1c52a7a14db554f188822a9d86237553a286592a72a45d754e050c7ea9b8b2735536300cbaa6a082df54d02032aa998218e9532164e2aa626063454c059476a979a2d3d52e404f92a5a644f154b0406f4a95851a1d52a184c3aa525cd6154a179206a939508cd52606312aa4a2c71f549070c42a918b2201522261ff2a42181905480109c8a8f88063d51e041fe2a3a183fb5470308bea8d87063551a04439aa324c70c546070c1ca8b8b0b21516080c52a2a0836854502858ca898406255120422b2a221c8e35440a844aa87830d8150e0a0c3aa1a08748543079890a85a8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness877Checked : PLift (checkWitnesses allPages fastPrime 877 witness877Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness877 : ∀ n, 877 ≤ n → n < 1002 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness877Checked.down

private def witness1002Data : ℕ := 0xee0b020c10716030a3e62c04345bc580440546b000307955ff043502bfc2876357f460b74afe081d815fb18534abf45849a57e43053eafc030db15f70814f2bec0c29d57d41967cafa1a10415f30a2da2be42036757c420ea4af80c03ed5ef024272bdc3c98d57b498d24af60a22b15eb204772bd44461d57a449010af40e0a5d5e7062462bcc18e6857957880aaf20520115e31c2d32bc4201da5784101f2af00114955df0e1492bbc0ca475774b03b2aee0210055db0a07c2bb40447f576430e68aec0c0a415d7061aa2bac105a05754403aaaea020a395d30633baba4286d857445906aae80f165d5cf104b1ab9c4c673573450a24ae60707515cb042372b941872e572460a1cae40714355c70e1faab8c14ecb5715a07e6ae20521d95c32050c2b84587e1570470fc0ae00e0d195bf082c1ab7c20a0d56f4b050aade031c815bb185472b74603ec56e428f00adc0d3ad95b7681f4ab6c146b956d4581e6ada01178d5b31238a2b64300f256c4081e2ad80123cd5af2422e2b5c1827c56b41867ead60407295ab0413d2b540c45a56a4309d6ad4072f3d5a73e4d92b4c541c956941188aad2221c0d5a3187a42b44f00ee568408ad6ad008139159f0e13a2b3c0c0ed5674089c2ace07288d59b2e1392b340c8d5566490df0acc0c1735597120762b2c04da5565560660aca0418f95931426aab241c32e5644201d4ac80109b158f061e42b1c14db1563569188ac6121e7158b1c5022b145c326562420aa0ac408

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1002Checked : PLift (checkWitnesses allPages fastPrime 1002 witness1002Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1002 : ∀ n, 1002 ≤ n → n < 1127 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1002Checked.down

private def witness1127Data : ℕ := 0x11eab408f1e2d680161772cfe0c9db59f8915eab3e963b0567c584ceacf64478359e858fccb3c8c0efd6780844c2cee3870659d8505d0b3a8323996741e1052ce60850659c83198cb389f23896701e4e92cde48ae759b8b0ee6b368b20bd66c1a27f2cd61859b59a838c28b34881db1668162282cce149c8599890fa8b328c113d6640a088acc60487e5988710fab308e13e16600c087acbe04b865978c875eb2e842b4165c2c0872cb60444c596828758b2c840435658024b72cae442d859581936ab2a9213a96540c4b52ca6445fd594840218b28812b196502c40aac9e343a8593820afcb268707fd64c044f82c964c10b5928085a4b24830b456480633aac8e2490b591880e86b228b042564402822ac8700d0c590910210b20810b2964006164ac7e0c57358f838f4cb1e8c1e9163c180fcac760839d58e8216beb1c992ac96382c2b82c6e1c99e58d891334b1a92312d6343c2b62c661c4cd58c830ad2b18870b05630063662c5e28ada58b8b9626b1698041562c0283e2c571065e58a849e26b14b20af962806396ac4e2c89b58987930eb12920e25624082b02c461c1f1588810caab10891af562014500ac3e504b9587830baab0e881ad561c143c82c36308d7586880704b0c842be1618302e72c2e202b358581895cb0a860df9614082122c26144235848290feb088f12b16100c0802c1e04b985838d93d8b069426ad60c263ecac1634376582820b88b04881c21608161542c0e0c1e8581811638b0299

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1127Checked : PLift (checkWitnesses allPages fastPrime 1127 witness1127Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1127 : ∀ n, 1127 ≤ n → n < 1252 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1127Checked.down

private def witness1252Data : ℕ := 0xbfab7f07363d6fd404b9adf83c7f45bec5895eb7d0504d56f90211eadf0081345bdc0966eb7b1508e96f5044582de834a0c5bcc899dcb791d12ad6f10a11b2de0086fb5bbc4965ab771512a56ed0a5d8add85c3325bac18800b75041dd16e9141192dd0083315b9c192bab730f0ffd6e508251adc8141305b8c08ddeb710915756e10c1962dc00c55b5b7c3045cb6f02302d6dd32116adb808d9a5b6d08938b6d050fe56d908096adb004d945b5d0912eb6b0d04b16d50277e2da8ac12b5b4c09c08b692423a56d11c1902da00cd8a5b3d0863eb670329116cd242a5ad98184935b2c287e4b65042e216c92e413ad90306655b1c40448b63020c5d6c5066132d8868a825b0c98db2b610917516c10e2a0ad80187bc5afc5903ab5f0c44556bd8e49c2d783c1255aec08248b5d011b4d6b9125bd2d705ca245adc907ccb5b0412016b50a39c2d68287ae5acc587c8b590411f96b10a186ad600ce2b5abd310d2b570d20456ad181ef2d581021f5aac114d0b55131ccd6a9141ed2d50104755a9c2823eb5301047d6a5021812d480c3d75a8c212d8b511011c56a10a42ead40343d55a7c214b4b4f133fb569d6e708ad38983d25a6c214b0b4d130bf56990610cad3008a9c5a5ca023cb4b0125856952008ead28042fa5a4c19bc2b49250be5691064812d203ca945a3ca0ff4b470c18f568d106ed2d18942155a2c10b60b45073ab168956109ad10087f25a1c60fe0b430c18c9685104542d0838e855a0d50232b4101

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1252Checked : PLift (checkWitnesses allPages fastPrime 1252 witness1252Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1252 : ∀ n, 1252 ≤ n → n < 1377 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1252Checked.down

private def witness1377Data : ℕ := 0x1180bbd8c053577a021342ef2085be5de0318ccbbb981da1776124c5aeea38e2c5dd10924ebb98d290d772207a0aee2a4b245dc099172bb78c196176e0e3aeaeda245b85db031306bb58e34d976a382832ed214a8c5da088a08bb38528d1766206992eca70d6f5d90e8ca0bb187052976202327aec21c2625d8010872baf8425c975e1c608aeba5c2615d7010da4bad88097d75a04562aeb2481485d60084bcbab8220d1756163242eaa1c6cd5d5041586ba9920d75752060a32ea204b935d40a8c88ba7871b1574e104b22e9a381445d3008c82ba58729bd74a2239dae922435a5d20189daba3851ce574612638ae8a647bf5d10512b2ba18e0d5d7420659f2e82503565d0018f72b9f8a10a973e081a9ae7a0c6385cf039db4b9da7050573a026f82e7284eb45ce1309c4b9b853d6d73658317ae6a1c2525cd0114b2b99910d35732060a02e62044de5cc0294aeb97911ea172e145532e5a4894d5cb070842b9584093572a04355ae522013e5ca008694b938321e1726183102e4a1c58a5c9030d52b91882b61722261a3ae420c6a85c8040b0cb8f86133971e0a390ae3a246a55c7040c30b8d87091d71a0409d2e32046135c6038272b8b8104e171602545ae2a48d135c50e882cb8984182d7120e4972e22386995c404150ab8792091170e043892e1a24dc25c310930ab858f1e5170a14400ae122cb8e5c20b0e1ab83891039706086f22e0a888535c10612fcb818f2885702221212e020833a5c00199f8b7f9d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1377Checked : PLift (checkWitnesses allPages fastPrime 1377 witness1377Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1377 : ∀ n, 1377 ≤ n → n < 1502 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1377Checked.down

private def witness1502Data : ℕ := 0x1258bfc0c05b17f7023032fec189ee5fd470c0abfa0615857f30a4ca2fe434de25fc4e82d4bf80120e97ef145a62fdc484775fb420f90bf6091f1d7eb120b4afd4046015fa431f36bf42905a17e702576afcc446a65f9439a10bf219059d7e30269eafc4687ba5f844a1cebf03734117df322fc2fbc181665f7408a9cbee0517cd7db0c395afb420aa15f64802c8bec013ab57d744571afac445f15f54302c6bea010a257d3043d62fa4249755f4469cfabe82105897cf0234aaf9c1c7a95f3449474be60f17b17cb0c4b5af9434b765f2498a84be4051c757c7100afaf8c0453f5f142873cbe2032db97c32682b2f84c48925f0458e2ebe0083ed17bf56230af7c1068f5ef43872abde0311817bb08445af742cee35ee520f36bdc090e517b7060aeaf6c04e905ed511c14bda1f0e4d7b30622daf64103925ec418e12bd80823a97af187452f5c8815c5eb409422bd60f056d7ab0277caf549438c5ea419832bd41617697a70c4722f4c304545e9420710bd2031e4d7a31233caf441ce565e8508a5abd005313d79f2e55daf3c443855e7419d42bce2314a579b0a663af3464b945e64a04e4bcc020559797022e82f2c181555e5409b7ebca1e1e2579312337af241c5245e44291a4bc80c0df578f06379af1c208ce5e3460f04bc609301578b2c290af14145205e24286f0bc4033d397875242caf0c2c44a5e1420a3abc20517157830c6a9af04706e65e04417f8bc01624c977f1a497aefc347ed5df45029cbbe01

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1502Checked : PLift (checkWitnesses allPages fastPrime 1502 witness1502Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1502 : ∀ n, 1502 ≤ n → n < 1627 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1502Checked.down

private def witness1627Data : ℕ := 0x1320c3a8c2ef58742437d30e61c3ea61c8194c8c388e1be58700e48b30de2c18461b808308c3681060d86c0215eb0d608d0361a8b96c4c34910af18680415db0ce0909c6199787cac32831bc18640e70830c6701816188087c6c308312ed860080c030be043e06178199eac2e9734cd85c304be30b630ba96168907b8c2c830f6d858063c6b0ae20dd06158d95f0c2a900f65854065d130a64817f614808f10c28880f61850061ebb09e0c2b1613810dc6c26870ac184c047743096844ad6128207a8c24830f4d848067e1308ea02ae6118102fcc22813665844342c6b086143d0610818b18c2085190d8400c0beb07e0477660f84079cc1e83129d83c0854c30763c2a760e8102f6c1c810a95838040bd306e0486d60d850ff6c1a892e1183424435306628c5060c8a8c78c188615fd8300a1e5305e0c3c860b819b08c169a289582c1c31b305618d8260a8d0af6c148505dd828028d8b04f041766098096f8c12921b318240e829b046b829e608810d94c108732118202c315b03e18a16607870c52c0e86284d81c1c59030364462760683119ec0c8b29f58181e467302e2c84e60585128ac0a8c233181416679b0266074c604841192c088b1f8d81012425301e28a73603878530c068205cd80c0235c30161ce2d6028f1bf2c049d18658080c244b00e109a260186995cc0297185d8040c1dbb0060c486600820528c008205bd80002149affe083b45ff819266bfe8c30917fc2a5d2aff64c16d5fe80a03ebfcad

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1627Checked : PLift (checkWitnesses allPages fastPrime 1627 witness1627Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1627 : ∀ n, 1627 ≤ n → n < 1752 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1627Checked.down

private def witness1752Data : ℕ := 0x12ecc790b316d8f12658bb1e03c19d63bc09dbec771e31618ed263a031d81c6a263ac30d42c750621918e9120ce31d004fae639d20d3cc730614318e5080cdb1c804b0f638c785d2c71020ba18e10428431c010d68637cb9da8c6f1e29498dd1a17331b8082e5636c121b2c6d2f34618d92c208b1b00cc02635c91496c6b0d14058d50842bb1a824e6d634ce155ac690e29298d11a46db1a028198633c085c2c670234418cd2c46cb19828731632c3832cc65012aa58c91c8543190b4195631c089f2c630436f98c5320ca318804c3e630c99386c610c30ed8c126468b18028be862fc92140c5f2d28d58bd1a34531781884462ec48f94c5d0810118b9062e4b1701494f62dc59190c5b0a30b98b52667db1685904762cd51e58c59213d898b146341b160187c062bc405aec57020b598ad042e131581419162ac08f76c550820f58a91270ab1506c9ae629c60e36c530726b18a5188a3b148d9058628d5983ac51130b4d8a1047beb14090bd6627c91716c4f1132a989d2a69531385d113626da2076c4d2a40e5899541fd31300c2ce625c109bec4b040fe1895060c631280418c624c08316c490119c58910c45a3120285b6623c28cdcc4706358988d30163b1180866c622c30cd6c450627fd8891a163311008bc9621c9058ac4302325d8852a53a310838ebb620cf958ec410f2c7588120161b100089fc61fc68cc8c3f0627e987d1a455b0f828cd361ecb07dcc3d0319858790c410b0f02466061dc3114ac3b0a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1752Checked : PLift (checkWitnesses allPages fastPrime 1752 witness1752Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1752 : ∀ n, 1752 ≤ n → n < 1877 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1752Checked.down

private def witness1877Data : ℕ := 0x1ce8cb79a20c196e10190b2da08dc465b0b836ecb58143e996a5a883b2d2b8d4565a0aa1c2cb3ac41059664c45e32ca2431d659010a96cb1842521962146fd32c260e6c6580d036acaf813b4995e38220b2ba0c9b9657058c40cad85151d95a084dbb2b22c6da65603116acab8924fd956146f932aa60822655041bdeca99837b995230764b2a270791654039362ca78b37a594e30713b29a649af653059456ca58c0c5594a040d832920443865201886eca38338899463257a328a38a2665106086cca18310d1942063c232821c1ae6500095dcc9f8e269d93e16187b27a0860764f028864c9d83229d93a1254ab272341ac64e008d94c9b8635a59362c647b26a4c30a64d01142ac998c22819321218432620889d64c04860cc97823db192e4268ab25a54ae564b070a64c95843cb592a3e505325230a0964a06085ec93832479926143b7324a1c42d649018bf8c918531fd9222661b324248a02648060352c8f811ae991e0c295b23a102fe6470113fcc8d8c30bd91a243b0b2321c6b4646030350c8b813b419163a401b22a20ad4645070a4ec8984149991208358b2221890964405110cc8789340190e2a719b21a68881643048ffac8588069590a0217c321208a6d6420685eec83821d499060e4f7b20a30fa26411185eac81820689902020d13202041a1640008342c7f8127a58fe1869a31fa5851b63f02033ec7d811fc18fa10533b1f23474963e0391f2c7b8a29818f61a86831eab914d63d1a083ac7983

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness1877Checked : PLift (checkWitnesses allPages fastPrime 1877 witness1877Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness1877 : ∀ n, 1877 ≤ n → n < 2002 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness1877Checked.down

private def witness2002Data : ℕ := 0xe52cf6062a819eb1839433d41858b67a420692cf4024b419e7a26d0b3cc5490b679449c36cf21716219e3086abb3c45087267844068ccf00226619df1448233bc244666774190dacee0807399db023edb3b41c46467641839acec0135419d7282c0b3ac107d7675439c18cea173a0d9d33292c33a5088fd674448faace80715f19cf08545339c3071967343150ece60c3ea59cb4032e339414ffb672511d60ce41a44ed9c75c42fb38c208f767144930cce20a44819c35a857b384a0658670429bfece01727ed9bf1653fb37c30bb066f479eeecde1f36f19bb2c8fcb374e885566e440e16cdc063dd59b73e4fab36c2c33d66d410ca2cda0511659b3065fbb36440e3966c4c22e0cd83125dd9af145d3335c3cfc066b508c98cd605115d9ab060e4335404a7266a460e06cd40635d99a72a8ab334cc0e2d6694c159ecd20d33619a3267b433447c56a66842038ecd0011ec199f0e712b33c601c6667408c8ccce053be199b382b333341045166641866accc02276999716322332c14d1b6654a1e84cca1e070d9930246a3324246426644294bccc80c258198f144ec331c2d14b6635813accc60b369198b2c0dfb31405132662578de4cc4060cbd987040deb30c04ccd661498abccc20437459832e591b304387a1660439992cc0130ca997f04225b2fc0c63a65f428892cbe0331c997b2466232f44cf7665e501980cbc13155197708372b2ec1832765d410aa4cba04307197322755b2e46c8c265c448648cb802

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2002Checked : PLift (checkWitnesses allPages fastPrime 2002 witness2002Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2002 : ∀ n, 2002 ≤ n → n < 2127 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2002Checked.down

private def witness2127Data : ℕ := 0x13bcd348a16fda680825134ce0d1ac6999803ccd32812d41a641a8f234c6d0372698810ecad308629b1a60166b034be4c1e469780893ed2e832061a5c0e4aa34b6245ba6968218c2d2c903781a582a3afb4ae18f0e6958d102cd2a871d71a540c1b734a608cb6694889d38d28984239a50487d3349e78a65693858930d2683125da4c062dab496111db6929a1e08d249a2745a4814844b48e9101e69190939cd228a46bda44621b33486081e269080a07ad20a21251a4006564347e309cd68f8503c0d1e8144b5a3c56598b4763474d68e831f3cd1c9e3b21a383287fb46ea4b2f68d869894d1a900775a34022d6b46610c4968c880d20d18850d79a3004246b45e0cd3c68b898d1ad1685122da2c0624534560c48968a819146d1488076da28020edb44e04be368987a05ed12a20d71a240424334460ce056888b1370d108a1a19a200a39e343e184836878186b4d0e821205a1c0669734364cfdb6869006b0d0c8235f1a18280ec342e041d7685809254d0a891691a140852034262d024684912330d08b124a1a101223e341e0cdb36838a9562d068c0759a0c0223cb4160cedb6828d08f0d048335c5a082833c340e14aae6818619aad02921671a04082cdb40610a2e680858b32d00842221a001097433ff4c91f67f84910acfe881cc19fc0c441b3f62088267e8418eccfc912dc99f81c55433ee301d367d8096decfa8e07499f40243e33e620ece67c8d1546cf88c36999f02a43d33de20bcc67b878b1ccf684

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2127Checked : PLift (checkWitnesses allPages fastPrime 2127 witness2127Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2127 : ∀ n, 2127 ≤ n → n < 2252 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2127Checked.down

private def witness2252Data : ℕ := 0x1578d730b1371ae5066fa35c8504db6b8c19c80d71151365ae106862b5c0909a36b7c490a2d6f07135dadd067d0b5b870dec6b6ca03f4d6d013155ad91e6d5b5b04c1f96b5c09ddcd6b180e71ad5041cdb5a808b976b4c68bd0d69043d9dad1360fbb5a0048fb6b3c41090d670728a1acd141cb359808e6e6b2cb1332d6509329dac9207f73590789976b1c49e7cd631a2655ac5123cd358818fbb6b0ce83ead61012871ac114265b5800caaa6afc597c2d5f0e1b2dabd0a41fb5781c5e16aec20d90d5d050e45ab9045893570303906adc1071ed5b022e05ab51a676b56844aa46acc59a82d591207c9ab10274d35605c5dc6abc20986d57033739aad28837b55888ce66aac88bb2d55041e55aa90c26035500cd3b6a9c92190d5325362daa5267983548689826a8c49d98d511834d5aa12435db540141ef6a7c09602d4f0c3231a9d2066eb5384529a6a6e18708d4d0245b5a9958745b5305c4b66a5c18706d4b022beda951877db528651d46a4d9190ed49103be5a9132258b5200c9716a3c48700d470212c1a8d067d1b51874af36a2c6220cd45282349a891054335102c1ec6a1c083d6d43014541a8556416b5081c6ad6a0c296c8d410d3079a811e41535001cf6969fce13dad3f0a259da7d127b334f870db669eca1a3ed3d123e61a793a6d934f0506aa69dc286ecd3b022d71a751a4b134e8241e969cc08b86d390431bda71205ac34e034ae669bc61c76d371607a1a6d0283934d88cb5469ac6a32ed352f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2252Checked : PLift (checkWitnesses allPages fastPrime 2252 witness2252Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2252 : ∀ n, 2252 ≤ n → n < 2377 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2252Checked.down

private def witness2377Data : ℕ := 0xa2adb1832541b621010736c204bdc6d8069946daf8f0835b5e02288b6ba0cfe16d70e0e1adad8518a1b5a081e1b6b2083c26d601210adaba04849b566410636aa0494b6d5041880da98e251db5210383b6a214d516d40893acda78942f1b4e4453b369a28cf16d3080a10da5832d9db4a18759b692585076d2018c3ada3843d29b4632778368a5cf496d10ca4ccda1b92f4db421a80336827488f6d0039a8cd9f913dc1b3e346ce367a485006cf018fbad9d8624e9b3a1061536723888c6ce038c2ed9b841859b3608774b66a5c6146cd022160d99a20819b320237e3662149c96cc049b24d97923c71b2e30533365a289c76cb04840ad958113e9b2a06863b6528cc226ca071e80d93991f3db260c610364a383b06c90118fed918f1bd5b220a63f36423c9296c80409eed8f8331edb1e1e56ab63a2c4f56c70189e8d8d833a6db1a2c27936320cf916c60d959cd8b8b0809b16027f5362a74e586c50a9d2ed899634a5b122252ab622286ea6c4028dd2d87851801b0e083e2361a18fe46c30e89d8d85833cd9b0a325a1361230ac96c205923ad838817f5b060848db60a20b3f6c1060754d81822469b0210100b602050546c01023ecd7fb22cedafe181d3b5fa08d1a6bf088bead7d843dfdafa3637135f2147b36be030f64d7b862185af60e3d8b5ea184e36bd01874ad79821ebdaf20c48735e2209a86bc048be0d77843019aee1c7eab5da747ac6bb03147ed758a2699aea1227035d20c9a56ba0483f6d7381

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2377Checked : PLift (checkWitnesses allPages fastPrime 2377 witness2377Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2377 : ∀ n, 2377 ≤ n → n < 2502 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2377Checked.down

private def witness2502Data : ℕ := 0xe8adf0052b09bdf144c7b7bc20b3d6f7459038dee062359bdb0e8d4b7b4a506b6f64f0cbadec04320dbd71c29e37ac0cd426f5482088dea1d2065bd30c59c37a42cb366f4458cb4de8043d51bcf30468379c1cb326f345a5bcde64338d1bcb265d9b794307376f24299b4de40f14ddbc70632b378c10e306f1498ca8de2043ad5bc32a1f13784088126f04307c2de0023ca5bbf2e8cdb77ca43df6ef411b20dde110881bbb02848b7747c3dd6ee411a60ddc103d3dbb7306c6376c451366ed5292f0dda080879bb302327376410a0e6ec449cd4dd8140f65baf045d1b75c30ba16eb461ddadd61625c1bab105cfb754311316ea529b0cdd41134a1ba720324b74c103d66e941163edd20b3195ba31c82ab7447821c6e8409736dd00c371db9f244b4b73c208076e7432290dce263f49b9b3610d373404bff6e64697fcdcc0d3f3db97361e8b72c08b166e5458c88dca040f3db9304401b7241918d6e4549a32dc81032fdb8f1e10c371c043ce6e3411ffedc61c345db8b2065eb7143c8006e243079adc402085db8702291b70c0cb876e1460a44dc20332e9b831e4adb704212016e058042cdc0014471b7f4a727b6fc507206df429970dbe0f2c15b7b16659b6f43c7f96de432080dbc1e2e05b771828f36ec0c7f56dd432306dba2918e5b730831bb6e41051c6dc418a34db8030849b6f0228cb6dc0c5186db418a2edb6032791b6b12655b6d43cbdf6da468c60db4042a0db671457e36cc2c62e6d9420fd6db206

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2502Checked : PLift (checkWitnesses allPages fastPrime 2502 witness2502Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2502 : ∀ n, 2502 ≤ n → n < 2627 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2502Checked.down

private def witness2627Data : ℕ := 0x1e0ce2e953771c5c2257bb8b628849716831ceee2c931029c5804204b8ae0856f715818adce2a8308f9c54024e138a62091471483a058e289b08f1c5002578389e28406713811a48e268f315dc4c1a8e33896a5111712910ad0e248308e5c480275c388e50d21711878d10e228408ddc4402711b88648b75710859214e20872ba5c40145b9387e2cd1c70f878806e1e821a11c3c0885d38767c90570e838ac8e1c831009c3804341386e10ef270d8aa482e1ab132e5c341c75738665056270c8195c8e188a3869c30247c3385e6077270b8296d2e168b3aa1c2c2811838560456070a818edee1485398dc28265ec384e3022f709808cf2e12841da5c240a730b8464cfb07088ca0c4e109d2959c201233b383e103fd707810ab4e0e8323e1c1c0e82fb8367455870681a3fce0cad3c81c182c685382e3c5557058196bce0a8b3825c142481c38267022c704809348e088823c5c100e6b4b81e40fda7038d2234e06a33415c0c1e475b8161c22a702809c10e049230e1c081a3abb80e14756701828a9ce02833f61c043447438061cdfe700890a9ae00834021c00361fa37fe08fd36ff8d0cd2dfe84459dbfc4c113b7f604e4d6fe8991cadfc871999bf80864ab7ee38d5a6fd880ea0dfa851525bf40641437e61899b6fc841850df88d0fc1bf0043a5b7de146646fb820448df68128f1bec124cb37d62074a6fa82968cdf48b1989be80861237ce343ed6f9811686df28b2ef9be41841037c6190256f88e0a80df083

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2627Checked : PLift (checkWitnesses allPages fastPrime 2627 witness2627Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2627 : ∀ n, 2627 ≤ n → n < 2752 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2627Checked.down

private def witness2752Data : ℕ := 0x206ce6d1a3289cd91a557b9b024eff735ca1ae2e6b0f2cd5cd514599b9a828f9a734cb884ee69021675cd10621339a008aac733c493fae67081669ccd0670ab99844597732c18d60e65042ee9cc916128b99004884731c30d5ee63043261cc51a732b98848424730c10b2ae610349b5cc16492eb980c442272fc113e6e5f08359dcbd1e91bb978b824f72ec0849ce5d013989cb9248c939709459272dc19764e5b0b397dcb52472f396848aa272cc49cb8e591227a9cb11012639600442072bc1083ee57022c91cad144f439582024b72ac09536e55092a69ca91284fb95075274729d99754e530b1e81ca50a60a394830c88728c69f70e51183559ca11e3cf3940149e0727c40494e4f012c69c9d1489c39388924c726d813b8e4d080925c990220db9300886b725c30d46e4b043fa1c95325d039282cedc724ca10d0e49063535c911e433392018865723c30d40e47041a7dc8d082bf39180cc75722c698e8e450d1a75c8908976391100415721c11e36e43151a69c85086a1b9083d2f4720e09fbce41190915c8102585b9002857771fc199aee3f0e34fdc7d1e6d038f840b0871ec50824e3d023011c791878b38f054b9271dc59502e3b092e45c75163c9b8e81485a71cc3081ee39023b35c7128600b8e030c0071bc6081ce37024495c6d44633b8d834fd671acc8486e35012149c690c804b8d06884f719c3081ae330229edc651212138c804920718c39ec6e31171031c6104348b8c010af9717c50ae2e2f03

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2752Checked : PLift (checkWitnesses allPages fastPrime 2752 witness2752Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2752 : ∀ n, 2752 ≤ n → n < 2877 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2752Checked.down

private def witness2877Data : ℕ := 0x15c4eab8936bdd561e45fbaaa18bee7550595c0ea989380dd522056fbaa2246e2754021492ea788498dd4e5e5b83a9a28dfc7530821f0ea59e1115d4a047513a92488bb7520323c6ea3a7318dd46184c4ba8a1d2ed7511e22a6ea1a13e51d422c3f2ba8214df97500804cce9f811109d3e046fbba7a40cd474f068880e9d823171d3a1821fba720905774e0d15a4e9b892d95d36144c0ba6a1cdf374d081470e998828d9d321021e3a620843b74c011be2e9790333dd2e1a4beba5a1cacc74b04915ee958625edd2a0e9903a530ce9474a091b36e938f1b5dd26084bcba4a1cd2f7490718a2e918c3d2dd222a4ba3a421c5b3748018daae8f842f65d1e167dcba3a5d146747108face8d8528a9d1a10514ba3220b5a7460504c0e8b81097dd160221aba2a08f7c7450b21cae899e3d15d122a3e9ba2214433744012092e879a1b41d0e0865e3a1a3425d74300a4c2e85b045e1d0a463e6ba12148a774203188ce838c16a5d06064523a0a18966741039d04e81923a05d02249033a02a85a774001957ee7f89096dcfe0250a39fa205a573f01979ce7d8b10c5cfa0455eb9f224fa773e0b979ae7b8b2d25cf614360b9ea10cb173d069960e798d42e1cf23a5a3b9e22924473c170d80e77843f6dcee307b539da58d7d73b07885ce75821af9cea083df39d214c3973a06085ae73820961ce602502b9ca20ca5739069ce4e71921af1ce208859b9c274f647380b0f70e6f8535ddcde1e4aab9ba1c7b5737029674e6d8a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness2877Checked : PLift (checkWitnesses allPages fastPrime 2877 witness2877Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness2877 : ∀ n, 2877 ≤ n → n < 3002 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness2877Checked.down

private def witness3002Data : ℕ := 0x1630eea093d4ddd3288c03ba4849bd774439378ee8074665dcf447c93b9c5427d77340975eee60a1c39dcb084dd3b941c813772429e46ee413475ddc74a53f3b8c21213771541f8eee2164cb9dc38453e3b8420c9f7704611d4ee0063c7ddbf2664ebb7c310b576f4d8bbeede0329dddbb1064d3b7430d7b76e47101cedc05239ddb70c7433b6c4445876d412274eda1f4b5ddb3707fe3b645d05976c4c9830ed80b38c5daf207fd3b5c5c45576b4123a4ed6252389dab0c8573b546c5d876a4191beed40609ddda702648bb4c30c157694591b8ed2062c09da31213abb4404275768409cf6ed01139e9d9f222eb3b3c0ce7876748a3a0ece252019d9b0a5ccbb3428e76766488ba6ecc032369d970c6453b2c3110b7654f15fceca0945add93421393b2404272764409ad8ec80e387dd8f20138bb1c0504d7634c84e0ec6011bddd8b08852bb146c8d37624320fcec41a1bd9d87085c6bb0c292b97615b1b76ec20f172dd83063ffbb0414e70760489810ec00b3579d7f1c52d3afc2099f75f438de2ebe042bb1d7b1263cbaf430f0375e49a334ebc2309b9d7702136baec04f3b75d4a1196eba062329d730c6dc3ae43d12175c4fa38aeb8253c01d6f266ac3adc385c675b41a028eb618404dd6b305c03ad42826a75a40a32aeb4234509d6740373bacc10f617594aa17ceb21c2945d6310372bac4108c37584316faeb00a293dd5f10526babc20447757410fdaeae051fb1d5b0a8acbab484446756411d4eeac12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3002Checked : PLift (checkWitnesses allPages fastPrime 3002 witness3002Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3002 : ∀ n, 3002 ≤ n → n < 3127 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3002Checked.down

private def witness3127Data : ℕ := 0x22ccf289f1cd9e50086dcbc9e38ab67938423ccf26a446fde4c4470c3c963d0987928c88faf24823c5de48248b13c8e7d0dc7918d97b4f228a3849e441e3023c860cc5a79085a172f209a2ac1e40107de3c7e5460278f819c1ef1e8f0a35e3c025ebbc762892678e83155af1c882495e380c41b3c6e149e278d839e1af1a921805e3406629bc662c9e178c839d78f189111cde30045a23c5e2483378b829064f16853349e2c187dabc5654e6678a881238f14864355e2836626bc4e2cfb27898a8bf6f1283434de2436237bc46092ac788991230f1086245de200c933bc3eb11b2787911c0ef0e8f4149e1c302fb3c360cda7786871fd6f0c96244de180c700bc2e3c912785830e54f0a842cd5e1412416bc261446c7848122eaf08a020ade100a54f3c1e2128a783979cb2f06904de1e0c9c77bbc16491547828f9218f0486367de081c144bc0e04725781820e48f02840a21e04025963c0625172780901ca8f00900a1de00028b8bbfe8082577f8293a0efe87273ddfc0e1433bf604ef277e891ca0efc901195df804411bbee1501777d8b9780efa8a30f5df41665bbbe63116977c900e3cef88423f9df00c231bbde08d9577b871396ef6872ef5dec14141bbd6052d677a9b9d3eef4912eedde81440dbbce14c33779859512ef2884275de43438c3bc610bb9778850e2cef0843badde0246f2bbbe3c7157778211f2eee864d09ddc88860bbb66ce477768821c0eec9c42fddd83658dbbae251227758f1d26eea91

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3127Checked : PLift (checkWitnesses allPages fastPrime 3127 witness3127Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3127 : ∀ n, 3127 ≤ n → n < 3252 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3127Checked.down

private def witness3252Data : ℕ := 0x15c2f67082569ecd0c7fc3d98550967b2cc0942f650244adec9387273d903c76a7b1c212aef63062b79ec51056ebd88207667b0c21fe6f6115361dec11a150bd80050957afcc23d8f5f233fc5ebd2a6c23d7834a277aec39de8f5d111d89eb9088143d70586357adc190c6f5b051d81eb5086c0bd6834ddf7acc715acf59084ad5eb1625bf3d60248607abc292a4f57061265ead04318bd580c75b7aac21fcef55153419ea9184a8bd501862e7a9c190bcf53052869ea50e3ad3d481085d7a8c28eb0f51043a61ea1206413d402cb747a7c49902f4f0b18a9e9d0642c3d38152e27a6da9ebcf4d133d75e9926867bd306829b7a5c09420f4b072151e950a63ebd282d0847a4cc092af49024af5e91644283d201501a7a3cb0534f47013e81e8d287723d1844dcc7a2c7109af45052da9e891271bbd103c6227a1c197eaf430a33c1e85185f9bd0828fd97a0ca9096f4105123de81048ed3d008d13779fce97d6f3f0a33b1e7d186753cf83121979ed319d0f3d0c3b65e7922423bcf01484679dc2a42cf3b2624f5e750c3a33ce81127879cd61accf390d3595e711a6b23ce034c6c79bc59f2cf3714358de6d1a7403cd84074479ac20c2ef3503357de691a8363cd060741799c21b82f330e2f89e6514908bcc898612798c18e7cf31042d6de6112242bcc008484797c11b7af2f0e0a49e5d027c7bcb850e20796c7a208f2d1c24c1e590c3063cb00cd59795c6a4a4f2b2a4391e5536304bca80cc62794c58c10f2903

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3252Checked : PLift (checkWitnesses allPages fastPrime 3252 witness3252Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3252 : ∀ n, 3252 ≤ n → n < 3377 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3252Checked.down

private def witness3377Data : ℕ := 0x2518fa5ab3111f4a149acbe930522d7d2128990fa38239f9f461e4513e8a148a17d10294c6fa1872631f420c95bbe82bd14e7d00e113ef9f853511f3e1815fbe7a042be7cf00898af9d823501f3a186643e722c65b7ce019cf2f9b8f226df360a44d3e6a144c27cd011612f99882c1df321086bbe626501c7cc0a9f34f97934229f2e2e44b3e5a144bf7cb01097cf95824629f2a3c44abe521504c7ca0b186ef938a446df263644a3e4a153917c926a030f91952eadf22127cbbe424c4ba7c8010572f8f810ae1f1e02448be3a150157c70a8970f8d8230c9f1a14705be32391167c60d856cf8b814c75f1672529be2a1caff7c5042342f899f12d1f12047a63e22484b37c401233cf879f1939f0e06763be1a4088a7c302a302f859e3f31f0a284b9be12190a67c20c0568f838134adf06182583e0a090c97c10c92def81863b11f02205cf3e0224f8d7c00992daf7f860ac5efe025793dfa212727bf1515def7d884029efa2a1583df204e647be079d74f7b900abdef6023c0bdea10f847bd09a00ef79954bcdef26a323bde20d30e7bc1c0efef7784306deee1443dbdda14f807bb09855af75812e59eea127a1bdd2492a27ba1724dcf73aa37ddee61c1563dca042ab7b90090eef7185400dee22a1553dc204f797b809a0c4f6f9712a1ede0443abdba150617b70b9472f6d87257deda0c2533db20925a7b6148c80f6b832579ed60c2523daa088707b50290def698528c5ed20e77f3da2452297b41312b8f6786

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3377Checked : PLift (checkWitnesses allPages fastPrime 3377 witness3377Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3377 : ∀ n, 3377 ≤ n → n < 3502 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3377Checked.down

private def witness3502Data : ℕ := 0x1f9afe4130b65fc7022773f8c0920a7f151118afe20535fdfc3183e13f8410d7e7f04609d4fe0022a59fbf0e6383f7c291dd7ef501526fde072a45fbb0ea21bf75fc6807ee419e0afdc102a3dfb70e33fbf6c0cc6a7ed451d54fda0f33c9fb31688f3f6468f027ec4824eafd82819f5faf0633e3f5c0ca8c7eb439ae8fd60c3931fab1c33d3f540d0787ea4b09cafd40235c9fa71899c3f4ce8dd87e9469510fd2073a91fa31e4d53f44190737e84b219afd018138df9f048383f3c592d17e7581c90fce0e428df9b2e88a3f34682d07e640859efcc014e35f97948b03f2c70f3d7e54899cafca0b44fdf93368023f2450ea07e44799c8fc80b4699f8f3c62ebf1c288b87e34297a8fc6093ce9f8b2245b3f14142cc7e240a5bafc4312f49f8712165bf0c04bd07e14489b4fc20219c1f830662cbf04290347e04a9164fc0053ce1f7f2262b3efc28dc87df46964efbe083a59f7b1e71e3ef438a7a7de4394f0fbc073cd1f772262a3eec28e387dd470cd4fba031e8df73086aebee430bca7dc4489a8fb802134df6f048183edc552c97db580588fb6014561f6b385913ed4204d17da411d1cfb40f3eb1f67268bbbecc74a707d9438f3efb20429b9f630e5e33ec4250c07d84c0f3afb0043551f5f183323ebc0d3667d7618584fae012c65f5b104cb3eb418f2a7d6488cc6fac032f05f571295dbeacbce267d5472394faa200b05f53024c93ea4187987d442114cfa8052c55f4f10849be9c5d1027d34d188afa60a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3502Checked : PLift (checkWitnesses allPages fastPrime 3502 witness3502Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3502 : ∀ n, 3502 ≤ n → n < 3627 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3502Checked.down

private def witness3627Data : ℕ := 0x5df022813b860441e3f44086105138108124b3020a546c20403a6d6c07e309db80f8311e101e85144203c04607c07624e1380e86981d01c8923b60380a3f3c06e1134180d9c8a1f01a822db603410833c06654da980c861b510188c40ce03028924405e90aba80b83a6c9016bf276602c0c285c056087e580a821c1b0148d470e0283c691404e2d0f58098c23b10129f142a02404284c04608f5f808889f51010923b5a0201e603c03e251408078d259900eae347a01c168304036549d48068305cd00c81141601804601c02e2502e8058a252100aa91a5e01406738c02638fec80489a4c5008a6300a0101246f401e142e4803808a050068240aa00c28737c01638c908028505c7004811f72008083edc00e112408019225c9002b013f6004041714006051828008e0fb5000842aae0000e5fdbffe24d967ff860d28ffe832fe5ffc125fc3ff6249ca7fe8311b0ffc850b81ff80227dbfee08f9f7fd891fbeffa932aa5ff40e3ea3fe610ec67fc8797e4ff8892fc5ff0126c73fde30df87fb869f32ff6922a9dfec0e3e8bfd610fdc7fa899388ff48645e9fe8388983fce68c807f9851d84ff28f4ab5fe45891cbfc690ebf7f887a25eff09a47edfe0423463fbe0d0b77f78b9a0efee8b492dfdc4a5a73fb6209be7f68317cafec8913cdfd8042793fae08a9e7f5838d12fea834b35fd45e906bfa6882dc7f4809696fe88831cdfd01416dbf9e04fd17f389918efe6852a65fcc0e2783f96084ef7f2810f8afe484

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3627Checked : PLift (checkWitnesses allPages fastPrime 3627 witness3627Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3627 : ∀ n, 3627 ≤ n → n < 3752 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3627Checked.down

private def witness3752Data : ℕ := 0x14250610649c20c14a29a4180090f382fcb8d8505f033c420bd1e82dc17850f0f82ec7a51b05d2720360b908620c1702492382dc2901905b044dda0b58061fc1682514182ccca1870591614c60b1047cac1604480b82bc20603057013c1e0ad1e7a3c15840dcb82ac60a610550244f60a932297c15008b9d829c41407053062e720a510722c1483452d828c10a590510235560a116500414018d54827c5999504f0a2e6a09d108c341386c6b7826c1a54d04d2930c609912295413008529825c115af04b07457a09534294412808c2c824c492230490538fe0911a662c1202890f823c29f1504711413a08d287c3c11844d4c822c599830450a2b4e0890e8e041107508f821caa3470431c42360852a71b410834b8f820c422f90411b32fa0811471ac10034b8c81fc41f9303f122e2a07d104fcc0f81890681ec29efd03d1127e20790c86dc0f05c52281dc11f8d03b123bce0751e5c2c0e8207fc81cc2184303909421a0712a56540e01cdba81bc605ed0370147ae06d3e35640d80c90081ac2a7ad0355732d20691496dc0d0b9260819d29b6f0330c34e20651684140c8549eb818c318350310945da0613647e40c01507f817caa5cd02f2f34d605d163f9c0b8102f3816c09dd902d0f305a059127b8c0b0447f1815c220f702b153a1e0551c710c0a8349e5814c30fdf0290445ce05136698c0a02ce1e813c68fdd02704145a04d0486840985c6a7812c185e30250149fe0494e178409004e1c811c691e902305

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3752Checked : PLift (checkWitnesses allPages fastPrime 3752 witness3752Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3752 : ∀ n, 3752 ≤ n → n < 3877 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3752Checked.down

private def witness3877Data : ℕ := 0xa9f09f8231a213e12191427a04cff84f051b1b09d8b33f613a144a742721523c84e10962309b87380a13618370c26a0d22484d1021690999520ba1320882142624cf2b84c07a10f09794362612e168c2425a68a4584b03063d09581319212a1298bc252c494c84a029295093850c72126022a5424a0932a84919928d0918525161220a18dc24204e6b84806a00b08f9233d211e14582423a1d2dc8471622ff08d9a3b4611a1c9f042335894484602904d08b8428f61160c8bec22a68941845028db708983151a112048d042226cbc3844041785087883ff610e2483bc21a50c58843048a890858241d610a28919421284bbf842041e490838f24f21060a40fc20a10faa8410894610818644061022e6bd42022c53f840011eb307f9041ba0fe2836b41fa0c53e83f0118a507d8948c20fa426f441f230ff683e091af107b8b3d620f62040d41ea10d7583d05862907981454a0f2329e541e34431383c0086270778131320ee1296141daad0a283b0a8da5075830c4a0ea0218941d2050a183a0a9bc70738c0c460e60251141ca18bb58390417690718828820e20c29d41c20853983801176506f8814e20de04496c1ba14cd9837050d9f06d8328760da0c36741b20c53683601143706b860c3a0d6025d6c1aa20bac835041bb70698c45be0d2346ecc1a230a19834031ad70678b0c320ce02814c19a4c30b833008617065810c2a0ca0250bc19218dd5832060d890638320420c6088fc418a7c308831009ba90618c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness3877Checked : PLift (checkWitnesses allPages fastPrime 3877 witness3877Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness3877 : ∀ n, 3877 ≤ n → n < 4002 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness3877Checked.down

private def witness4002Data : ℕ := 0x21a90de151c161bb0619cc37404bef86e4417db0dc08325a1b712382436c0d37086d5d97d50da0844b21b32e7f1c3644456e86c411a530d80a1c0a1af0674ec35c3433886b40866f0d601349e1ab142b6c3540930086a569a4d0d40a2ce61a70e380434c0cd2586945191f0d20944a61a32e535434418be6868440dff0d0031bfa19f0637ec33c0c842867420acf0ce02467619b34420c33410f908664812d10cc053a4a1971a5f0c32c20c8b865449a410ca0a1bf219306977c324b11238644b86690c8010cd218f0268e431c2883e8634221f30c6160cce18b024b2c3141533f8625a14c30c406321618712746c30c34b2a86143a4630c220465a183347c643044134c8605b14bb0c006345a17f1488cc2fc5c56385f4116510be072f7617b1080ec2f44833185e409d130bc0d38661771837a42ec0c83c85d42164d0ba0738521731868942e428c7a85c449f070b81048ba16f4094c42dc9921b85b4f9a230b60a343e16b1441dc2d410e8485a4692b10b405343a16714376c2cc0d2e785956239d0b21c20e216308590c2c41ca56858430dd90b0034cc215f66194c2bc051cc8574e1ef10ae104abe15b502acc2b4092888565290690ac04155e157045eac2ac20556855411e6f0aa0f254e1530a419c2a410f35854479a130a80a365e14f1673c429c352c48535525270a626154e14b042a9429408ede85247064b0a4013dd214720824428c4d2a185153a5090a22531a6143128e44284711c78504e1e5f0a00f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4002Checked : PLift (checkWitnesses allPages fastPrime 4002 witness4002Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4002 : ∀ n, 4002 ≤ n → n < 4127 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4002Checked.down

private def witness4127Data : ℕ := 0x209f11c924efe2389054fc46e192fb88d958e4f11a831c9a23406952c46694b6688c83a727118bf375e230166adc45e2928688b918b1311682395e22c1843a44561034888a80a097114923eea22820878444e5499c88982a547112a5304a22410911444678871888821ba51108b161622004391443e0d32b8879824b910ea147c221c38729443630d5288685212110c934cce218627b0442e3ca928858322dd10a9837362141685dc42650b60884839327108853af62101a902c41e751b68838d22d110698160220c046a7441628eb98828696bb104871c7220806902440e7521d8818f1e3b1028e263a2040a605c4062057d880811a911008a439a2002a8da43fe6871a87f819c970fe8c2d5e1fc0e89f43f65c57b87e8123d30fc9c3ffa1f8226a1c3ee2898a87d828af50fa824b3e1f45265643e624dc587c858af10f8822a121f00c654c3de2471487b8193110f68532a21ec1281e43d64898687a829c8d0f48c47fe1e83a65343ce252178798f130b0f2853c561e41c72243c630710878819a750f08a1c3e1e0062bac3be09242877901c850ee8c4c161dc5a78a43b6383418768086830ec8136f21d8161a043ae0533e8759990ad0ea8441c61d42697543a6ac574874810e150e88347de1d03a4bfc39e14b4887383a3570e69a3c321cc1c19ec39604f0b8728722b90e498456e1c83019dc38e04c9c87184a3bd0e29c2fda1c41019d43860506a8708994eb0e08621321c00864cc37e251a886f8d16810de87

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4127Checked : PLift (checkWitnesses allPages fastPrime 4127 witness4127Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4127 : ∀ n, 4127 ≤ n → n < 4252 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4127Checked.down

private def witness4252Data : ℕ := 0x1fcb15b1047462b5349704568a0ac08acc320db15912463a2b1308f7c5606cabe8abc30b4d157021d0e2ad067f1455840c428aac421b51551426ee2a90a7f045504089e8a9c21cf91530c338e2a5125c845481cce28a8c48e7b15103337e2a11290fc54074d808a7c50e7514f0337f629d169f945394c9b68a6c2913314d040d6629902901453070ab98a5c31dd514b0d26d22950a7c745283cc3c8a4c4214f14913336e291124d9c520151348a3cb26c5147363cf228d1c813451844ab88a2c31f111450f2ade2890c9924510b8ab58a1c30b45143023b8a2851a869450850b828a0c3a313141180d56281024d6c5001505d89fc9156713f064c8a27d5c7c144f83cfd489ec8112113d043e062791e94f44f090d7389dc51fa113b100d4a27502616c4e82102089cc89ae31390a433a27128615c4e020e6d89bc616ff137073cca26d1c98a44d8b473289ac1a0b71351248b22693c4d4c4d015157899cb9bd51330b0d3e265022ccc4c808b7b898c3869d1310135c2261145bcc4c01cb78897c39daf12f0d2dde25d0e7e544b8410fc896ca8e6112d03379e259166b6c4b028e65895c6274112b414a662554887dc4a854d6a894c50b27129022202251087e2c4a040f72893c7a1331271345ee24d3080b44984519f892cc983f1250848f62493e1a6449004ecf891c69f89123104046245228a8c4885cb6c890c39cc11210c26822410a2c844800901088fc8a1ed11f15163e23d04828447848e5b88ec61bbb11d0b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4252Checked : PLift (checkWitnesses allPages fastPrime 4252 witness4252Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4252 : ∀ n, 4252 ≤ n → n < 4377 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4252Checked.down

private def witness4377Data : ℕ := 0x23971999948763323878cc662352348cc0e9779197873a9632e1890e465a711e58cb0d0b7b19582431a32a26941c652851288ca0aa63f193ac3ec63261e3b3c64a0ce2f8c90595b91918638ba3221645ec64210e2c8c8059eaf18f8e2ee231e0e714c63a2cbb78c703a57918da5471231a327ab463238e288c605917518b842b663160c1b7c62a04d0b8c504a3c31899a3c4a3121a4ebc62214c608c404212518792389230e166d1c61a290f48c30a0ebb185834c9a30a5a7a8c612389d58c202916f183843c263061a1b6c60a04bae8c103a001181902b463020c922c602791a28c00c251d17fa20dae2fe02845c5fa48d028bf04a07d17d911d662fa06459c5f2108b18be0225f317ba94a022f6423aac5ea0cacd8bd031f491798f49522f23e98645e2ac9d08bc02a4fb177a14c2e2ee5695a45da951d68bb0d19f5175892ea22ea0e3a9c5d20c8ae8ba0221d91739448a22e63a9bec5cae4cf98b90499f1171892e922e20e935c5c28123f8b80f0ea316f8348322de38747c5ba30cf68b704939916d8516c62da048a2c5b2592518b60fa4d316ba040de2d6222d7c5aa08ff08b50806c71698136462d21477b45a234f9c8b40786c31678116ba2ce047a3459a392088b30e138d1658549e62ca427444592310798b20919d71638931262c6108b5458a5c8a98b1020e8f1618316ae2c2045624582190e38b00a21c515f9427062be0a623c57a209c08af0299cf15d8940c62ba227f34572411918ae0c1b1115b8a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4377Checked : PLift (checkWitnesses allPages fastPrime 4377 witness4377Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4377 : ∀ n, 4377 ≤ n → n < 4502 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4377Checked.down

private def witness4502Data : ℕ := 0x11c31d8043cc63af1a504475c14c928eb44140f1d60537263ab14815c754410ad8ea491a6f1d40947663a732581c74c18e558e945870d1d2010e1a3a3026474744210668e8488baf1d0023dee39f1c729c73c2d10d8e74a22891ce15437639b266e34734290ab8e64921551cc124192397221c2472c045d38e54120471ca1047d2393343c847240c8d98e44220451c81046f638f303c7c71c0cc898e3440f1d1c6032bea38b0c1c1471404f288e246a1531c4120e06387023c6470c0cc868e1440b9f1c2024bf63835090747046c78a8e0419a591c009459637f2c93f46fc803808df409edf1be0e459237b2c988c6f4a90d68de49a7351bc3c4b1e3774a2e5c6ec08e4a8dd459edb1ba0e46423732e3c346e40caf18dc4324131b81b0df236f028f946dc689f68db4293e91b6054b0e36b4a92846d478bcb8da43a6351b42b1e0636706575c6cc18f6b8d94713e31b205348e3631269146c4252f78d85418f11b0080dea35f022e446bc083798d74097911ae073c8635b1a2e3c6b4091338d64aa5531ac2348ea3573a46346ac10eb28d5460ef91aa032f1e3530e3bd46a40ce418d4458ef31a8030dde34f02866469c4cbc58d3438eef1a6034c0a34b5278f4694354168d26c98e31a408279e3470a71ec68c2c9e68d14295d11a2064dfe343706374684209e38d04286eb1a0014dfa33f708f5467c68e3a8cf45a31119e1731ae33b10958c674903748ce4093bf19c053aa633718807466c408c08cd421d4d19a0c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4502Checked : PLift (checkWitnesses allPages fastPrime 4502 witness4502Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4502 : ∀ n, 4502 ≤ n → n < 4627 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4502Checked.down

private def witness4627Data : ℕ := 0x745216811eaa42c06948c85680b2990a8324ad2149d4d82428621d0c84e052269098d9de32128c43fa424268c5c846587a790881a759210bd2ff64200e821c83e40e759078591ff20e8432d641c10519c836152a090690a74520cbb1e96418067fcc82e3ca2f90582873f20a8137ae414149a8c826bcb259048325ff208a717ae41004516c81e14d5d903848bd5206822fd240c0e5164816151ae9028b9feb2048f32be408105f8480e1cff4901878bcf202822fb24040e7f948063d1859008b0735200810e664000247d47fe112da8ff9287311fe8144923fc281cbc7f604a278fe8297d31fc870e563f802773c7ee30b1c8fd8325711faa33b9a3f4187f7c7e63d0888fc889dcb1f88c49963f03c5f3c7de1cdde8fb85217b1f692287e3ec0a8f447d664ca48fa8407291f4814e763e876878c7ce4c8f28f9821dbb1f28c399e3e416477c7c610d4f8f884a1df1f093178a3e00458a47be188ec8f78221db1ee93352e3dc1288c47b650ca18f68421011ec9132823d8106a4c7ae252d48f5928f2f1ea834dbe3d46888bc7a650d478f484a46b1e89c2c423d00c97b479e9ced88f386216d1e6924c363cc52875c7964cb0e8f28319371e488374e3c8142eec78e08bde8f18396191e28649ce3c43e8a6478654a0f8f08296151e08628363c00a8fec77e68a0b8ef829b9f1de8a176e3bc04769c77630d3e8ee849e671dc8d47f23b83464a476e20b068ed831cb51da8b4d9e3b466978c7669d2478ec8e99271d888

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4627Checked : PLift (checkWitnesses allPages fastPrime 4627 witness4627Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4627 : ∀ n, 4627 ≤ n → n < 4752 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4627Checked.down

private def witness4752Data : ℕ := 0x761255012d4e4a90c8d3c95058fc3929c70c0d25302452a4a52878c494830b51928c321bf25112385e4a11470b494029268927ce969f24f063a7a49d16709c93829220926cd234924d163efe4991c88749304cb4d925c320b924b10180e495043e5c9280cfbe924c71f7b2490e4d0e4915880cc9203cc17923c39eb92470d493a48d3893dc918787c9922c1a21924513360e489125a5491018e0e921c5246d2431b4782485308efc90860e95920c59e1d2410c442a4812649249001101291fc7a53923f20442247d26490c8f810a5491ec29e1523d0c1f0e479065a2c8f0185ff91dc1262723b2817fa475047db48e83928991ccf9e112390c3a46471167aac8e034fb391bc714a123705334646d1066848d820c1091ac3a4312351a17ee469042fd48d008e8c919c5a20b2331330364650e7a948c834cce918c407532310140364611e7d7c8c038ccb917c4167722f06303245d0e8df48b85d406916e8122b22d04464e4592c2fac8b0087b4915c1a37722b173d424551a80648a83ce00914c51f572290e302a4510e89cc8a050a48913c2966922706244244d08523489814efd912c62137225113bea44918661c89020cc2911c40be52230246ea4452e8b0c88854b30910c3148522105432e441249aa4880bcdfb90fc50f5b21f03290643d0a84bc8784543a90eef121121d044cea439582f7c8700930a90dd4245521b1b28fa4350a8234868412bf90cd19bed2190a17b6431043d5c8600d00290bc7920921704

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4752Checked : PLift (checkWitnesses allPages fastPrime 4752 witness4752Data 125 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4752 : ∀ n, 4752 ≤ n → n < 4877 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4752Checked.down

private def witness4877Data : ℕ := 0x3e265261a3f4ca4a0ce449490519fd2918818b252204762ca422d25e9480e1c8728f8a36b251e121e34a3a04f859470696e728d860f1651a028dcca32592c8946111d8728b8b46e25162c6d54a2a24ec094505a06b2898f45765122853f4a22152149440c87832878136a650e129ddca1af52769430ea4932859b4b1a50a4467bca1220b6b942031e4f2838c3c9a506188954a0a4c6249410114f32818546d65022c311ca02083be94000a24f27f9342064fe2075bc9fa2cc3a93f03a5d727da44b624fa4683ec9f240b6893e03266f27baa483e4f63294b49ea7c94393d020fc52798343ca4f22430f49e208e3293c051d632778b41ea4ee2030dc9da08c3493b039b3d27589186a4ea04674c9d22138493a1a223f273931f7e4e6066cec9ca2507493908252b2719f3dce4e21a49f49c2103ba93800986126f874cd24de54969c9ba8d38f9371b127726d8448964da347e749b23934f93616a5f126ba54d224d6581dcc9aa04b6193503204f2698f24e64d20885949a244d9893404a3dd2679824de4ce0830ac99a08c2993303926d265844cca4ca548754992493ae9321da0d3263904c6e4c650613c98a1d0e99310919c32618818424c20449a4982113569301720cb25f903c724be18612c97a1d31992f1416b325d863f224ba1c498c97210cdc92e0414c525b852d5a4b60c5aac96a183b292d0087652598144424b22652fc962147d292c01a68b257ac418e4ae203e7495a0c60892b01125725584

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def witness4877Checked : PLift (checkWitnesses allPages fastPrime 4877 witness4877Data 124 = true) :=
  ⟨by decide +kernel⟩

private theorem witness4877 : ∀ n, 4877 ≤ n → n < 5001 → GoodWitness n :=
  checkWitnesses_sound allPagesGood fastPrime_sound witness4877Checked.down

theorem complete : ∀ n, 2 ≤ n → n < 5001 → GoodWitness n :=
  (join_witness (join_witness (join_witness (join_witness (join_witness witness2 witness127) (join_witness witness252 (join_witness witness377 witness502))) (join_witness (join_witness witness627 witness752) (join_witness witness877 (join_witness witness1002 witness1127)))) (join_witness (join_witness (join_witness witness1252 witness1377) (join_witness witness1502 (join_witness witness1627 witness1752))) (join_witness (join_witness witness1877 witness2002) (join_witness witness2127 (join_witness witness2252 witness2377))))) (join_witness (join_witness (join_witness (join_witness witness2502 witness2627) (join_witness witness2752 (join_witness witness2877 witness3002))) (join_witness (join_witness witness3127 witness3252) (join_witness witness3377 (join_witness witness3502 witness3627)))) (join_witness (join_witness (join_witness witness3752 witness3877) (join_witness witness4002 (join_witness witness4127 witness4252))) (join_witness (join_witness witness4377 witness4502) (join_witness witness4627 (join_witness witness4752 witness4877))))))

end OMA.PrimeCountSums

theorem OMA.solution : OMA.R_OeisA238568_conjecture_5_R1.H1 := by

  intro n hn hmax
  exact OMA.PrimeCountSums.complete n (by omega) (by omega)