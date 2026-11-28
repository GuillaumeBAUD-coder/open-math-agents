import OMAReductions.R_oeis_a085264_R1

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


private theorem convolution_right (m n k : ℕ) (f g : ℕ → ℕ) :
    convolution m n f g k =
      ∑ j ∈ range n, if j ≤ k ∧ k - j < m then f (k-j)*g j else 0 := by
  unfold convolution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ k
  · have eq (i : ℕ) : k = i+j ↔ i = k-j := by omega
    simp_rw [eq]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hj, true_and]
  · have ne (i : ℕ) : ¬ k = i+j := by omega
    simp [hj, ne]

def squarefreeDigit (i : ℕ) : ℕ := if Squarefree i then 1 else 0

def squareDigit (i : ℕ) : ℕ := if 0 < i ∧ i.sqrt^2 = i then 1 else 0

private def squareRoster (N : ℕ) : Finset ℕ :=
  (range (N+1)).filter (fun i => 0 < i ∧ i.sqrt^2 = i)

theorem squareRoster_card_le (N : ℕ) : (squareRoster N).card ≤ N.sqrt := by
  have h : (squareRoster N).card ≤ (Icc 1 N.sqrt).card := by
    apply Finset.card_le_card_of_injOn Nat.sqrt
    · intro i hi
      have hm := Finset.mem_filter.mp hi
      rw [Finset.mem_range] at hm
      exact Finset.mem_Icc.mpr
        ⟨Nat.sqrt_pos.mpr hm.2.1, Nat.sqrt_le_sqrt (by omega)⟩
    · intro i hi j hj e
      have hi := (Finset.mem_filter.mp hi).2.2
      have hj := (Finset.mem_filter.mp hj).2.2
      exact hi.symm.trans (e ▸ hj)
  simpa [Nat.card_Icc] using h

theorem convolution_square_bound (N k : ℕ) :
    convolution (N+1) (N+1) squarefreeDigit squareDigit k ≤ N.sqrt := by
  rw [convolution_right]
  calc
    _ ≤ ∑ j ∈ range (N+1), squareDigit j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases pred : j ≤ k ∧ k-j<N+1
      · have h : squarefreeDigit (k-j) ≤ 1 := by unfold squarefreeDigit; split <;> omega
        simpa [pred] using Nat.mul_le_mul_right (squareDigit j) h
      · rw [if_neg pred]
        exact Nat.zero_le _
    _ = (squareRoster N).card := by simp [squareDigit,squareRoster]
    _ ≤ N.sqrt := squareRoster_card_le N

def representationCount (n : ℕ) : ℕ :=
  ((range (n.sqrt+1)).filter (fun k => 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2))).card

theorem convolution_square_eq (N n : ℕ) (h : n ≤ N) :
    convolution (N+1) (N+1) squarefreeDigit squareDigit n = representationCount n := by
  rw [convolution_right]
  let good (j : ℕ) : Prop := 0<j ∧ j.sqrt^2=j ∧ j<n ∧ Squarefree (n-j)
  let (j : ℕ) : Decidable (good j) :=
    inferInstanceAs (Decidable (0<j ∧ j.sqrt^2=j ∧ j<n ∧ Squarefree (n-j)))
  let support := (range (N+1)).filter good
  have fold :
      (∑ j ∈ range (N+1), if j≤n ∧ n-j<N+1 then squarefreeDigit (n-j)*squareDigit j else 0) =
      support.card := by
    rw [show support.card = ∑ j ∈ range (N+1), (if good j then (1:ℕ) else 0) by
      simp [support]]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < n
    · have hj' : j≤n ∧ n-j<N+1 := by omega
      by_cases jPow : 0<j ∧ j.sqrt^2=j <;> by_cases sf : Squarefree (n-j)
      all_goals simp [hj',hj,good,squarefreeDigit,squareDigit,jPow,sf]
    · by_cases he : j=n
      · subst j
        simp [good,squarefreeDigit, squareDigit]
      · have above : ¬ j≤n := by omega
        simp [good, hj, above]
  rw [fold, representationCount]
  refine Finset.card_bij' (fun j _ => j.sqrt) (fun k _ => k^2) ?forward ?backward ?left ?right
  case forward =>
    intro j hj
    have hx := (Finset.mem_filter.mp hj).2
    rcases hx with ⟨pos,square,below,sf⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt below.le)
    · exact ⟨Nat.sqrt_pos.mpr pos, by rwa [square], by rwa [square]⟩
  case backward =>
    intro k hk
    have hx := (Finset.mem_filter.mp hk).2
    rcases hx with ⟨pos,below,sf⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact ⟨by positivity, by simp [Nat.sqrt_eq'], below, sf⟩
  case left =>
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2.1
  case right =>
    intro k _
    exact Nat.sqrt_eq' k

theorem digit_square_representations {base N n : ℕ} (large : N.sqrt < base) (hi : n ≤ N) :
    pack base (N+1) squarefreeDigit * pack base (N+1) squareDigit / base^n % base =
      representationCount n := by
  rw [digit_mul _ _ (by omega) (fun j _ => (convolution_square_bound N j).trans_lt large) (by omega)]
  exact convolution_square_eq N n hi


def truncatedSquareDigit (cap i : ℕ) : ℕ :=
  if 0 < i ∧ i.sqrt^2 = i ∧ i.sqrt ≤ cap then 1 else 0

private theorem truncatedSquare_sum_le (cap count : ℕ) :
    (∑ i ∈ range count, truncatedSquareDigit cap i) ≤ cap := by
  simp only [truncatedSquareDigit, Finset.sum_boole]
  have h :
      ((range count).filter (fun i => 0 < i ∧ i.sqrt^2 = i ∧ i.sqrt≤cap)).card ≤ (Icc 1 cap).card := by
    apply Finset.card_le_card_of_injOn Nat.sqrt
    · intro i hi
      have hm := (Finset.mem_filter.mp hi).2
      exact Finset.mem_Icc.mpr ⟨Nat.sqrt_pos.mpr hm.1,hm.2.2⟩
    · intro i hi j hj e
      have hi := (Finset.mem_filter.mp hi).2.2.1
      have hj := (Finset.mem_filter.mp hj).2.2.1
      exact hi.symm.trans (e ▸ hj)
  simpa [Nat.card_Icc] using h

theorem convolution_truncated_bound (start m n cap k : ℕ) :
    convolution m n (fun i => squarefreeDigit (start+i)) (truncatedSquareDigit cap) k ≤ cap := by
  rw [convolution_right]
  refine le_trans (Finset.sum_le_sum (g := fun j => truncatedSquareDigit cap j) ?_)
    (truncatedSquare_sum_le cap n)
  intro j _
  by_cases pred : j ≤ k ∧ k - j < m
  · have small : squarefreeDigit (start+(k-j)) ≤ 1 := by
      unfold squarefreeDigit
      split <;> omega
    simpa only [if_pos pred, one_mul] using Nat.mul_le_mul_right (truncatedSquareDigit cap j) small
  · rw [if_neg pred]
    exact Nat.zero_le _

theorem convolution_truncated_le (start m n cap k : ℕ) :
    convolution m n (fun i => squarefreeDigit (start+i)) (truncatedSquareDigit cap) k ≤
      representationCount (start+k) := by
  rw [convolution_right]
  let good (j : ℕ) : Prop :=
    (j ≤ k ∧ k - j < m) ∧ (0 < j ∧ j.sqrt^2=j ∧ j.sqrt≤cap) ∧ Squarefree (start+(k-j))
  let (j : ℕ) : Decidable (good j) :=
    inferInstanceAs (Decidable ((j ≤ k ∧ k - j < m) ∧ (0 < j ∧ j.sqrt^2=j ∧ j.sqrt≤cap) ∧ Squarefree (start+(k-j))))
  let support := (range n).filter good
  have fold :
      (∑ j ∈ range n, if j ≤ k ∧ k - j < m then
        squarefreeDigit (start+(k-j))*truncatedSquareDigit cap j else 0) = support.card := by
    rw [show support.card = ∑ j ∈ range n, (if good j then (1:ℕ) else 0) by simp [support]]
    apply Finset.sum_congr rfl
    intro j _
    by_cases p : j≤k ∧ k - j < m
    by_cases q : 0 < j ∧ j.sqrt^2=j ∧ j.sqrt≤cap
    by_cases f : Squarefree (start+(k-j))
    all_goals simp [*, good, squarefreeDigit, truncatedSquareDigit]
  rw [fold, representationCount]
  apply Finset.card_le_card_of_injOn Nat.sqrt
  · intro j hj
    have jm := (Finset.mem_filter.mp hj).2
    obtain ⟨⟨loc,_⟩,⟨pos,sq,_⟩,sf⟩ := jm
    have nonzero : 0 < start+(k-j) := Nat.pos_of_ne_zero sf.ne_zero
    have jlt : j < start+k := by omega
    have eq : start+(k-j) = start+k-j := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,?_⟩
    · exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt jlt.le)
    · exact ⟨Nat.sqrt_pos.mpr pos, by rwa [sq], by rwa [sq, ← eq]⟩
  · intro i hi j hj e
    have hi := (Finset.mem_filter.mp hi).2.2.1.2.1
    have hj := (Finset.mem_filter.mp hj).2.2.1.2.1
    exact hi.symm.trans (e ▸ hj)

theorem digit_truncated_le {base start m n cap k : ℕ}
    (large : cap < base) (hi : k < m+n) :
    pack base m (fun i => squarefreeDigit (start+i)) *
      pack base n (truncatedSquareDigit cap) / base^k % base ≤
      representationCount (start+k) := by
  rw [digit_mul _ _ (by omega) (fun j _ => (convolution_truncated_bound start m n cap j).trans_lt large) hi]
  exact convolution_truncated_le start m n cap k

theorem pack_add (base count : ℕ) (f g : ℕ → ℕ) :
    pack base count f + pack base count g = pack base count (fun i => f i + g i) := by
  simp only [pack, Nat.add_mul, Finset.sum_add_distrib]

theorem pack_const (base count c : ℕ) (large : 2 ≤ base) :
    pack base count (fun _ => c) = c * ((base^count-1)/(base-1)) := by
  simp only [pack, ← Finset.mul_sum, Nat.geomSum_eq large]

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

def repeated (width count c : ℕ) : ℕ :=
  c * ((2^((width+1)*count)-1)/(2^(width+1)-1))

theorem repeated_eq_pack (width count c : ℕ) :
    repeated width count c = pack (2^(width+1)) count (fun _ => c) := by
  unfold repeated
  rw [pack_const, Nat.pow_mul]
  exact Nat.one_lt_two_pow (by omega)

def thresholdBits (word padding guards : ℕ) : ℕ :=
  (word+padding) &&& guards

theorem thresholdBits_eq_of_padded (width count level : ℕ) (f : ℕ → ℕ)
    (padded : ∀ i < count, f i + (2^width-level) < 2^(width+1)) (levelBound : level ≤ 2^width) :
    thresholdBits (pack (2^(width+1)) count f)
      (repeated width count (2^width-level)) (repeated width count (2^width)) =
        pack (2^(width+1)) count (fun i => if level ≤ f i then 2^width else 0) := by
  have highSmall : 2^width < 2^(width+1) := by
    have p : 0 < 2^width := by positivity
    rw [pow_succ]
    omega
  have indicators (i : ℕ) (_ : i < count) :
      (if level≤f i then 2^width else 0) < 2^(width+1) := by
    split <;> omega
  rw [thresholdBits, repeated_eq_pack, repeated_eq_pack, pack_add]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and,
    pack_testBit _ _ _ (by omega) padded j,
    pack_testBit _ _ _ (by omega) (fun _ _ => highSmall) j,
    pack_testBit _ _ _ (by omega) indicators j]
  by_cases inside : j/(width+1) < count
  · simp only [if_pos inside]
    by_cases high : j%(width+1) = width
    · rw [high, Nat.testBit_two_pow_self, Bool.and_true]
      by_cases marked : level ≤ f (j/(width+1))
      · rw [if_pos marked, Nat.testBit_two_pow_self]
        exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (padded _ inside)
      · rw [if_neg marked, Nat.zero_testBit]
        exact Nat.testBit_lt_two_pow (by omega)
    · have hg : (2^width).testBit (j%(width+1)) = false :=
        Nat.testBit_two_pow_of_ne (Ne.symm high)
      by_cases marked : level ≤ f (j/(width+1)) <;> simp [hg,marked]
  · simp [inside]

theorem thresholdBits_eq (width count level : ℕ) (f : ℕ → ℕ)
    (bound : ∀ i < count, f i < 2^width) (levelBound : level ≤ 2^width) :
    thresholdBits (pack (2^(width+1)) count f)
      (repeated width count (2^width-level)) (repeated width count (2^width)) =
        pack (2^(width+1)) count (fun i => if level ≤ f i then 2^width else 0) := by
  apply thresholdBits_eq_of_padded width count level f _ levelBound
  intro i hi
  have := bound i hi
  rw [pow_succ]
  omega

def equalLevelBits (width count level word : ℕ) : ℕ :=
  let guards := repeated width count (2^width)
  thresholdBits word (repeated width count (2^width-level)) guards ^^^
    thresholdBits word (repeated width count (2^width-(level+1))) guards

theorem equalLevelBits_eq (width count level : ℕ) (f : ℕ → ℕ)
    (bound : ∀ i < count, f i < 2^width) (levelBound : level < 2^width) :
    equalLevelBits width count level (pack (2^(width+1)) count f) =
      pack (2^(width+1)) count (fun i => if f i = level then 2^width else 0) := by
  have highSmall : 2^width < 2^(width+1) := by
    have p : 0 < 2^width := by positivity
    rw [pow_succ]
    omega
  unfold equalLevelBits
  dsimp only
  rw [thresholdBits_eq _ _ _ _ bound (by omega), thresholdBits_eq _ _ _ _ bound (by omega)]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  have h0 (p : Prop) [Decidable p] : (if p then 2^width else 0) < 2^(width+1) := by
    split <;> omega
  rw [pack_testBit _ _ _ (by omega) (fun _ _ => h0 _) j,
    pack_testBit _ _ _ (by omega) (fun _ _ => h0 _) j,
    pack_testBit _ _ _ (by omega) (fun _ _ => h0 _) j]
  by_cases inside : j/(width+1) < count
  · simp only [if_pos inside]
    let v := f (j/(width+1))
    change ((if level≤v then 2^width else 0).testBit (j%(width+1)) ^^
      (if level+1≤v then 2^width else 0).testBit (j%(width+1))) =
      (if v=level then 2^width else 0).testBit (j%(width+1))
    by_cases h : v=level
    · simp [h]
    · by_cases hv : v<level
      · have not1 : ¬ level≤v := by omega
        have not2 : ¬ level+1≤v := by omega
        simp [h,not1,not2]
      · have yes : level≤v := by omega
        have next : level+1≤v := by omega
        simp [h,yes,next]
  · simp [inside]

theorem pack_append (base a b : ℕ) (f : ℕ → ℕ) :
    pack base (a+b) f = pack base a f + base^a*pack base b (fun i => f (a+i)) := by
  unfold pack
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

theorem pack_slice {base count offset width : ℕ} (f : ℕ → ℕ) (positive : 0 < base)
    (bound : ∀ i < count, f i < base) (within : offset+width ≤ count) :
    pack base count f / base^offset % base^width =
      pack base width (fun i => f (offset+i)) := by
  let tail := pack base (count-offset) (fun i => f (offset+i))
  have decomp : pack base count f = pack base offset f + base^offset*tail := by
    rw [← pack_append, Nat.add_sub_of_le (by omega)]
  have first : pack base offset f < base^offset := pack_lt_pow f (fun i hi => bound i (by omega))
  have quote : pack base count f / base^offset = tail := by
    rw [decomp, Nat.add_mul_div_left _ _ (pow_pos positive _), Nat.div_eq_of_lt first, zero_add]
  rw [quote]
  let slice := pack base width (fun i => f (offset+i))
  have sliceSmall : slice < base^width := pack_lt_pow _ (fun i hi => bound _ (by omega))
  have tailSplit : tail = slice + base^width*pack base (count-offset-width) (fun i => f (offset+(width+i))) := by
    dsimp only [tail,slice]
    rw [← pack_append, Nat.add_sub_of_le (by omega)]
  rw [tailSplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt sliceSmall]

theorem threshold_full_iff_of_padded (width count level : ℕ) (f : ℕ → ℕ)
    (padded : ∀ i < count, f i + (2^width-level) < 2^(width+1)) (levelBound : level ≤ 2^width) :
    thresholdBits (pack (2^(width+1)) count f)
      (repeated width count (2^width-level)) (repeated width count (2^width)) =
        repeated width count (2^width) ↔
      ∀ i < count, level ≤ f i := by
  rw [thresholdBits_eq_of_padded _ _ _ _ padded levelBound, repeated_eq_pack]
  constructor
  · intro checked i hi
    have h := congrArg (fun n : ℕ => n / (2^(width+1))^i % 2^(width+1)) checked
    have positive : 0 < (2:ℕ)^(width+1) := by positivity
    have highSmall : 2^width < 2^(width+1) := by
      have p : 0 < 2^width := by positivity
      rw [pow_succ]
      omega
    have checkSmall (j : ℕ) (_ : j < count) :
        (if level ≤ f j then 2^width else 0) < 2^(width+1) := by
      split <;> omega
    rw [digit_pack _ positive checkSmall hi,
      digit_pack (fun _ => 2^width) positive (fun _ _ => highSmall) hi] at h
    by_contra bad
    rw [if_neg bad] at h
    exact (pow_ne_zero width (by decide : (2:ℕ) ≠ 0)) h.symm
  · intro h
    unfold pack
    apply Finset.sum_congr rfl
    intro i hi
    simp only [if_pos (h i (Finset.mem_range.mp hi))]

theorem threshold_full_iff (width count level : ℕ) (f : ℕ → ℕ)
    (bound : ∀ i < count, f i < 2^width) (levelBound : level ≤ 2^width) :
    thresholdBits (pack (2^(width+1)) count f)
      (repeated width count (2^width-level)) (repeated width count (2^width)) =
        repeated width count (2^width) ↔
      ∀ i < count, level ≤ f i := by
  apply threshold_full_iff_of_padded width count level f _ levelBound
  intro i hi
  have := bound i hi
  rw [pow_succ]
  omega

theorem representation_lower_window_padded {width start m n cap offset count level : ℕ}
    (capSmall : cap+(2^width-level) < 2^(width+1)) (levelSmall : level ≤ 2^width)
    (within : offset+count ≤ m+n)
    (checked :
      thresholdBits
        ((pack (2^(width+1)) m (fun i => squarefreeDigit (start+i)) *
            pack (2^(width+1)) n (truncatedSquareDigit cap)) /
          (2^(width+1))^offset % (2^(width+1))^count)
        (repeated width count (2^width-level)) (repeated width count (2^width)) =
          repeated width count (2^width)) :
    ∀ i < count, level ≤ representationCount (start+offset+i) := by
  let coefficients := convolution m n (fun i => squarefreeDigit (start+i)) (truncatedSquareDigit cap)
  have padded (i : ℕ) : coefficients i + (2^width-level) < 2^(width+1) :=
    (Nat.add_le_add_right (convolution_truncated_bound start m n cap i) _).trans_lt capSmall
  have wider (i : ℕ) (_ : i < m+n) : coefficients i < 2^(width+1) := by
    have := padded i
    omega
  have product :
      pack (2^(width+1)) m (fun i => squarefreeDigit (start+i)) *
        pack (2^(width+1)) n (truncatedSquareDigit cap) =
          pack (2^(width+1)) (m+n) coefficients := pack_mul _ _ _ _ _
  rw [product, pack_slice coefficients (by positivity) wider within] at checked
  have good := (threshold_full_iff_of_padded width count level (fun i => coefficients (offset+i))
    (fun i _ => padded (offset+i)) levelSmall).mp checked
  intro i hi
  exact (good i hi).trans (by
    simpa only [Nat.add_assoc] using convolution_truncated_le start m n cap (offset+i))

theorem pack_truncated_squares (base cap count : ℕ) (fits : cap^2 < count) :
    pack base count (truncatedSquareDigit cap) =
      ∑ k ∈ Icc 1 cap, base^(k^2) := by
  unfold pack
  simp only [truncatedSquareDigit, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun i _ => i.sqrt) (fun k _ => k^2) ?forward ?backward ?left ?right ?value
  case forward =>
    intro i hi
    have hm := (Finset.mem_filter.mp hi).2
    exact Finset.mem_Icc.mpr ⟨Nat.sqrt_pos.mpr hm.1,hm.2.2⟩
  case backward =>
    intro k hk
    have hm := Finset.mem_Icc.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,?_⟩
    · exact (Nat.pow_le_pow_left hm.2 2).trans_lt fits
    · have positive : 0 < k := by omega
      exact ⟨pow_pos positive 2, by simp [Nat.sqrt_eq'], by simpa [Nat.sqrt_eq'] using hm.2⟩
  case left =>
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2.1
  case right =>
    intro k _
    exact Nat.sqrt_eq' k
  case value =>
    intro i hi
    have eq := (Finset.mem_filter.mp hi).2.2.1
    simp only [eq]

end OMA.PackedConvolution

namespace OMA.PackedConvolution

open Finset

/-- Dividing out a common positive coefficient factor preserves the packed positions. -/
theorem pack_div_scalar (base count scalar : ℕ) (f : ℕ → ℕ) (hp : 0 < scalar) :
    pack base count (fun i => scalar * f i) / scalar = pack base count f := by
  unfold pack
  simp_rw [Nat.mul_assoc]
  rw [← Finset.mul_sum, Nat.mul_div_cancel_left _ hp]

/-- Every radix place has residue one modulo one less than the radix. -/
theorem pack_mod_pred {base count : ℕ} (f : ℕ → ℕ) (hp : 0 < base) :
    pack base count f % (base-1) = (∑ i ∈ range count, f i) % (base-1) := by
  have residue (a b : ℕ) : (a + base*b) % (base-1) = (a+b) % (base-1) := by
    have split : base*b = b+(base-1)*b := by
      calc
        base*b = ((base-1)+1)*b := congrArg (fun t => t*b) (by omega)
        _ = _ := by ring
    rw [split, ← Nat.add_assoc, Nat.add_mul_mod_self_left]
  induction count generalizing f with
  | zero => simp [pack]
  | succ count ih =>
    rw [pack_succ, residue, sum_range_succ']
    calc
      _ = (f 0 % (base-1) + pack base count (fun i => f (i+1)) % (base-1)) % (base-1) :=
        Nat.add_mod _ _ _
      _ = _ := by rw [ih, ← Nat.add_mod, add_comm (f 0)]

theorem level_cardinality {base mask count : ℕ} (f : ℕ → ℕ)
    (hp : 0 < base) (hdigits : ∀ i < count, f i ≤ 1) (hcount : count < base-1)
    (hpack : mask = pack base count f) :
    ((range count).filter (fun i => f i = 1)).card = mask % (base-1) := by
  have hsum : (∑ i ∈ range count, f i) = ((range count).filter (fun i => f i = 1)).card := by
    calc
      _ = ∑ i ∈ range count, if f i = 1 then 1 else 0 := by
        apply sum_congr rfl
        intro i hi
        have h := hdigits i (mem_range.mp hi)
        split <;> omega
      _ = _ := by simp
  have hcard : ((range count).filter (fun i => f i = 1)).card < base-1 := by
    exact (card_filter_le _ _).trans_lt (by simpa using hcount)
  rw [hpack, pack_mod_pred f hp, hsum, Nat.mod_eq_of_lt hcard]

/-- A unit digit in a radix of size `2^lane` is detected at its first bit. -/
theorem lane_bit_eq_one {lane mask count i : ℕ} (f : ℕ → ℕ)
    (hlane : 0 < lane) (hdigits : ∀ j < count, f j ≤ 1) (hi : i < count)
    (hpack : mask = pack (2^lane) count f) : mask.testBit (lane*i) = true ↔ f i = 1 := by
  have hbase : 1 < (2 : ℕ)^lane := Nat.one_lt_two_pow (by omega)
  have hdiv : 2 ∣ (2 : ℕ)^lane := dvd_pow_self 2 (by omega)
  have hread : pack (2^lane) count f / (2^lane)^i % (2^lane) = f i :=
    digit_pack f (by omega) (fun j hj => (hdigits j hj).trans_lt hbase) hi
  rw [hpack, Nat.testBit_eq_decide_div_mod_eq, pow_mul, ← Nat.mod_mod_of_dvd _ hdiv,
    hread, Nat.mod_eq_of_lt (by have := hdigits i hi; omega), decide_eq_true_eq]

theorem maximal_index_of_bits {lane mask count endpoint : ℕ} (f : ℕ → ℕ)
    (hlane : 0 < lane) (hdigits : ∀ i < count, f i ≤ 1) (hend : endpoint < count)
    (hpack : mask = pack (2^lane) count f)
    (present : mask.testBit (lane*endpoint) = true)
    (after : mask >>> (lane*(endpoint+1)) = 0) :
    IsGreatest (((range count).filter (fun i => f i = 1)) : Set ℕ) endpoint := by
  constructor
  · exact mem_filter.mpr ⟨mem_range.mpr hend, (lane_bit_eq_one f hlane hdigits hend hpack).mp present⟩
  · intro i hi
    obtain ⟨hin, hval⟩ := mem_filter.mp hi
    by_contra! hgt
    have hle : lane*(endpoint+1) ≤ lane*i := Nat.mul_le_mul_left lane (by omega)
    let offset := lane*i-lane*(endpoint+1)
    have hz := congrArg (fun mask : ℕ => mask.testBit offset) after
    change (mask >>> (lane*(endpoint+1))).testBit offset = (0 : ℕ).testBit offset at hz
    rw [Nat.testBit_shiftRight, Nat.zero_testBit,
      show lane*(endpoint+1)+offset=lane*i by dsimp [offset]; omega] at hz
    have ht := (lane_bit_eq_one f hlane hdigits (mem_range.mp hin) hpack).mpr hval
    rw [hz] at ht
    contradiction

end OMA.PackedConvolution

namespace OMA.PackedConvolution

open Finset

private abbrev lowSize : ℕ := 187426
private abbrev lowBase : ℕ := 2^18
private abbrev lowHigh : ℕ := 2^17

def positiveLowLevel (coefficients ones level : ℕ) : ℕ :=
  let guard := (ones - 1) <<< 17
  let atLeast (j : ℕ) := (coefficients + (lowHigh-j)*ones) &&& guard
  (atLeast level ^^^ atLeast (level+1)) >>> 17

def lowFinset (level : ℕ) : Finset ℕ :=
  (Icc 1 187425).filter (fun n => representationCount n = level)

private def indicator (level i : ℕ) : ℕ :=
  if 0 < i ∧ representationCount i = level then 1 else 0

private theorem cutoff_root : (187425 : ℕ).sqrt ≤ 432 :=
  Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (by decide))

private theorem repr_small (i : ℕ) (hi : i < lowSize) : representationCount i ≤ 432 := by
  have hi' : i < 187425+1 := hi
  rw [← convolution_square_eq 187425 i (by omega)]
  exact (convolution_square_bound 187425 i).trans cutoff_root

private theorem coefficients_mod {base N cap squarefree squares : ℕ}
    (baseBound : N.sqrt < base) (capBound : N.sqrt ≤ cap) (fits : cap^2<N+1)
    (hsf : squarefree = pack base (N+1) squarefreeDigit)
    (hsq : squares = ∑ k ∈ Icc 1 cap, base^(k^2)) :
    squarefree*squares % base^(N+1) = pack base (N+1) representationCount := by
  have eq (i : ℕ) (hi : i < N+1) :
      truncatedSquareDigit cap i = squareDigit i := by
    have size := (Nat.sqrt_le_sqrt (by omega : i ≤ N)).trans capBound
    simp [truncatedSquareDigit, squareDigit, size]
  have hsq' : squares = pack base (N+1) squareDigit := by
    rw [hsq, ← pack_truncated_squares base cap (N+1) fits]
    unfold pack
    apply Finset.sum_congr rfl
    intro i hi
    rw [eq i (mem_range.mp hi)]
  rw [hsf, hsq', pack_mul]
  have subword := pack_slice (base := base) (count := (N+1)+(N+1))
    (offset := 0) (width := N+1) (convolution (N+1) (N+1) squarefreeDigit squareDigit)
    (by omega) (fun i _ => (convolution_square_bound N i).trans_lt baseBound) (by omega)
  simp only [pow_zero, Nat.div_one, zero_add] at subword
  rw [subword]
  unfold pack
  apply Finset.sum_congr rfl
  intro i hi
  change convolution (N+1) (N+1) squarefreeDigit squareDigit i * base^i = _
  have hi' := mem_range.mp hi
  rw [convolution_square_eq N i (by omega)]

theorem low_coefficients_mod {squarefree squares : ℕ}
    (hsf : squarefree = pack lowBase lowSize squarefreeDigit)
    (hsq : squares = ∑ k ∈ Icc 1 432, lowBase^(k^2)) :
    squarefree*squares % lowBase^lowSize = pack lowBase lowSize representationCount :=
  coefficients_mod (N := 187425) (cutoff_root.trans_lt (by decide))
    cutoff_root (by decide) hsf hsq

theorem low_coefficients_of_product {coefficients squarefree squares : ℕ}
    (product : coefficients = squarefree*squares)
    (hsf : squarefree = pack lowBase lowSize squarefreeDigit)
    (hsq : squares = ∑ k ∈ Icc 1 432, lowBase^(k^2)) :
    coefficients % lowBase^lowSize = pack lowBase lowSize representationCount := by
  rw [product]
  exact low_coefficients_mod hsf hsq

private theorem pack_remove_first (base n : ℕ) :
    pack base (n+1) (fun _ => 1) - 1 = pack base (n+1) (fun i => if 0 < i then 1 else 0) := by
  simp only [pack_succ, Nat.lt_irrefl, if_false, Nat.zero_add, Nat.zero_lt_succ,
    if_true, Nat.add_sub_cancel_left]

private theorem repeated_remove_first (w n : ℕ) :
    repeated w (n+1) 1 - 1 = pack (2^(w+1)) (n+1) (fun i => if 0 < i then 1 else 0) := by
  rw [repeated_eq_pack]
  exact pack_remove_first _ _

private theorem positive_repeated_remove_first (w n : ℕ) (positive : 0<n) :
    repeated w n 1 - 1 = pack (2^(w+1)) n (fun i => if 0 < i then 1 else 0) := by
  cases n with
  | zero => omega
  | succ n => exact repeated_remove_first w n

private theorem low_ones_sub {ones : ℕ} (ho : ones = repeated 17 lowSize 1) :
    ones - 1 = pack lowBase lowSize (fun i => if 0 < i then 1 else 0) := by
  rw [ho]
  exact positive_repeated_remove_first 17 lowSize (by decide)

private theorem bit_one (i : ℕ) : (1 : ℕ).testBit i = decide (i=0) := by
  change (2^0 : ℕ).testBit i = _
  rw [Nat.testBit_two_pow]
  by_cases h : i=0
  · subst i; rfl
  · have he : 0 ≠ i := Ne.symm h
    simp [h,he]

private theorem rank_threshold {coefficients ones level bit : ℕ}
    (hc : coefficients % lowBase^lowSize = pack lowBase lowSize representationCount)
    (ho : ones = repeated 17 lowSize 1)
    (hle : level ≤ lowHigh)
    (hit : bit/18 < lowSize ∧ 0 < bit/18 ∧ bit%18=0) :
    (coefficients + (lowHigh-level)*ones).testBit (17+bit) =
      decide (level ≤ representationCount (bit/18)) := by
  let pad := lowHigh-level
  have hlevel : level ≤ 131072 := hle
  have hp : pad*ones = pack lowBase lowSize (fun _ => pad) := by
    rw [ho, repeated_eq_pack]
    change pad * pack lowBase lowSize (fun _ => 1) = pack lowBase lowSize (fun _ => pad)
    simp only [pack_const _ _ _ (by decide : 2 ≤ lowBase), Nat.one_mul]
  have hb (i : ℕ) (hi : i < lowSize) : representationCount i+pad < lowBase := by
    have h := repr_small i hi
    change representationCount i + (131072-level) < 262144
    omega
  have padBound (i : ℕ) (hi : i < lowSize) : pad < lowBase :=
    (Nat.le_add_left pad (representationCount i)).trans_lt (hb i hi)
  have sum : (coefficients+pad*ones) % lowBase^lowSize =
      pack lowBase lowSize (fun i => representationCount i+pad) := by
    rw [Nat.add_mod, hc, hp, Nat.mod_eq_of_lt (pack_lt_pow _ padBound),
      pack_add, Nat.mod_eq_of_lt (pack_lt_pow _ hb)]
  have bitSmall : 17+bit < 18*lowSize := by omega
  have bitAddress : 17+bit = 18*(bit/18)+17 := by omega
  have eq := congrArg (fun w : ℕ => w.testBit (17+bit)) sum
  change ((coefficients+pad*ones) % (2^18)^lowSize).testBit (17+bit) =
    (pack (2^18) lowSize (fun i => representationCount i+pad)).testBit (17+bit) at eq
  rw [← Nat.pow_mul, Nat.testBit_mod_two_pow] at eq
  simp only [bitSmall, decide_true, Bool.true_and] at eq
  change (coefficients+pad*ones).testBit (17+bit) = _
  calc
    _ = (pack lowBase lowSize (fun i => representationCount i+pad)).testBit (17+bit) := eq
    _ = (representationCount (bit/18)+pad).testBit 17 := by
      conv_lhs => rw [bitAddress]
      exact pack_bit_in_lane 18 lowSize _ hb hit.1 (by decide)
    _ = _ := by
      by_cases h : level ≤ representationCount (bit/18)
      · simp only [h, decide_true]
        refine Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt ?_ (hb _ hit.1)
        change 131072 ≤ representationCount (bit/18)+(131072-level)
        omega
      · simp only [h, decide_false]
        apply Nat.testBit_lt_two_pow
        change representationCount (bit/18)+(131072-level) < 131072
        omega

private theorem low_level_pack {coefficients ones level : ℕ}
    (hc : coefficients % lowBase^lowSize = pack lowBase lowSize representationCount)
    (ho : ones = repeated 17 lowSize 1) (hle : level ≤ 100) :
    positiveLowLevel coefficients ones level = pack lowBase lowSize (indicator level) := by
  apply Nat.eq_of_testBit_eq
  intro bit
  change (positiveLowLevel coefficients ones level).testBit bit =
    (pack (2^18) lowSize (indicator level)).testBit bit
  unfold positiveLowLevel
  simp only [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  have h19 : 17 ≤ 17+bit := by omega
  simp only [h19, decide_true, Bool.true_and, Nat.add_sub_cancel_left]
  have guard :
      (ones-1).testBit bit =
      decide (bit/18 < lowSize ∧ 0 < bit/18 ∧ bit%18=0) := by
    rw [low_ones_sub ho, pack_testBit 18 lowSize (fun i => if 0 < i then 1 else 0)
      (by decide) (fun i _ => by split <;> decide)]
    by_cases i : bit/18 < lowSize <;> by_cases p : 0 < bit/18 <;>
      simp only [i,p,if_true,if_false, true_and, false_and, Nat.zero_testBit, bit_one,decide_false]
  rw [guard, pack_testBit 18 lowSize (indicator level) (by decide)
    (fun i _ => by unfold indicator; split <;> decide)]
  by_cases hit : bit/18 < lowSize ∧ 0 < bit/18 ∧ bit%18=0
  · have h1' : level ≤ lowHigh := by change level ≤ 131072; omega
    have h2' : level+1 ≤ lowHigh := by change level+1 ≤ 131072; omega
    rw [rank_threshold hc ho h1' hit, rank_threshold hc ho h2' hit]
    rw [if_pos hit.1]
    simp only [hit]
    by_cases eq : representationCount (bit/18) = level
    · have he : 0 < bit/18 ∧ representationCount (bit/18) = level := ⟨hit.2.1,eq⟩
      rw [indicator, if_pos he, bit_one]
      simp [eq]
    · have he : ¬(0 < bit/18 ∧ representationCount (bit/18) = level) := fun h => eq h.2
      rw [indicator, if_neg he, Nat.zero_testBit]
      by_cases lt : representationCount (bit/18) < level
      · have h1 : ¬ level ≤ representationCount (bit/18) := by omega
        have h2 : ¬ level+1 ≤ representationCount (bit/18) := by omega
        simp [h1,h2]
      · have h1 : level ≤ representationCount (bit/18) := by omega
        have h2 : level+1 ≤ representationCount (bit/18) := by omega
        simp [h1,h2]
  · simp only [hit, decide_false, Bool.and_false, Bool.false_xor]
    by_cases inRange : bit/18 < lowSize
    · rw [if_pos inRange, indicator]
      by_cases inside : 0 < bit/18 ∧ representationCount (bit/18) = level
      · have outside : bit%18 ≠ 0 := by omega
        rw [if_pos inside, bit_one, decide_eq_false outside]
      · rw [if_neg inside, Nat.zero_testBit]
    · rw [if_neg inRange]

private theorem indicator_set (level : ℕ) :
    (range lowSize).filter (fun i => indicator level i = 1) = lowFinset level := by
  ext i
  simp only [mem_filter,mem_range,mem_Icc,lowFinset,indicator,ite_eq_left_iff,
    zero_ne_one,imp_false,not_not]
  change i < 187426 ∧ (0 < i ∧ representationCount i = level) ↔ _
  omega

theorem low_data_from_gates (coefficients ones : ℕ)
    (hc : coefficients % lowBase^lowSize = pack lowBase lowSize representationCount)
    (ho : ones = repeated 17 lowSize 1)
    (freq last : List ℕ) (hf : freq.length ≤ 101) (hl : last.length ≤ 101)
    (validLast : ∀ i : Fin last.length, last.get i < lowSize)
    (counts : (List.range 101).all (fun v =>
      positiveLowLevel coefficients ones v % (lowBase-1) == freq[v]!) = true)
    (endpoints : (List.range last.length).all (fun v =>
      let mask := positiveLowLevel coefficients ones v
      let endpoint := last[v]!
      mask.testBit (18*endpoint) && (mask >>> (18*(endpoint+1)) == 0)) = true)
    (zeros : positiveLowLevel coefficients ones 0 = (1 <<< 18) + (1 <<< (13*18)))
    (freqZero : freq[0]! = 2) :
    lowFinset 0 = {1,13} ∧
      (∀ i : Fin last.length, IsGreatest (lowFinset i.val : Set ℕ) (last.get i)) ∧
      (∀ i : Fin freq.length, (lowFinset i.val).card = freq.get i) := by
  have digits (l i : ℕ) (_ : i < lowSize) : indicator l i ≤ 1 := by
    unfold indicator
    split <;> decide
  have cardEq (j : ℕ) (hj : j < 101) :
      (lowFinset j).card = positiveLowLevel coefficients ones j % (lowBase-1) := by
    rw [← indicator_set]
    exact level_cardinality (indicator j) (by decide) (digits j) (by decide)
      (low_level_pack hc ho (by omega))
  have getCount (j : ℕ) (hj : j < 101) :
      positiveLowLevel coefficients ones j % (lowBase-1) = freq[j]! := by
    exact beq_iff_eq.mp (List.all_eq_true.mp counts j (List.mem_range.mpr hj))
  refine ⟨?_,?_,?_⟩
  · have card : (lowFinset 0).card = 2 := (cardEq 0 (by decide)).trans
      ((getCount 0 (by decide)).trans freqZero)
    have has (i : ℕ) (hi : i=1 ∨ i=13) : i ∈ lowFinset 0 := by
      have bound : i < lowSize := by change i < 187426; omega
      have tested : (positiveLowLevel coefficients ones 0).testBit (18*i) = true := by
        rw [zeros]
        rcases hi with rfl | rfl <;> decide +kernel
      have h := (lane_bit_eq_one (indicator 0) (by decide) (digits 0) bound
        (low_level_pack hc ho (by decide))).mp tested
      rw [← indicator_set]
      exact mem_filter.mpr ⟨mem_range.mpr bound,h⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      exact has i (by simpa using hi)
    · rw [card]
      decide
  · intro i
    have h := List.all_eq_true.mp endpoints i.val (List.mem_range.mpr i.isLt)
    have e : last[i.val]! = last.get i := getElem!_pos last i.val i.isLt
    simp only [e, Bool.and_eq_true_iff, beq_iff_eq] at h
    rw [← indicator_set]
    exact maximal_index_of_bits (indicator i.val) (by decide) (digits i.val) (validLast i)
      (low_level_pack hc ho (by have := i.isLt; omega)) h.1 h.2
  · intro i
    exact (cardEq i.val (by have := i.isLt; omega)).trans
      ((getCount _ (by have := i.isLt; omega)).trans (getElem!_pos freq i.val i.isLt))

end OMA.PackedConvolution

namespace OMA.SquarefreeRepresentation

def primeRoster : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191]

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

def firstMultiple (start square : ℕ) : ℕ := (square - start % square) % square

def sieveBandStep (lane start last acc p : ℕ) : ℕ :=
  let square := p*p
  let offset := firstMultiple start square
  if offset ≤ last then
    let multiples := (repeatedBits (square * lane) ((last - offset)/square + 1)) <<< (lane * offset)
    acc ^^^ (acc &&& multiples)
  else acc

def squarefreeBand (lane start last : ℕ) : ℕ :=
  let all := repeatedBits lane (last + 1)
  primeRoster.foldl (sieveBandStep lane start last) (if start = 0 then all ^^^ 1 else all)


theorem firstMultiple_iff {square start i : ℕ} (positive : 0 < square) :
    square ∣ start+i ↔ ∃ q, i = firstMultiple start square + square*q := by
  have below : firstMultiple start square < square := Nat.mod_lt _ positive
  have startBelow := Nat.mod_lt start positive
  have divides : square ∣ start + firstMultiple start square := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    unfold firstMultiple
    by_cases z : start % square = 0
    · simp [z]
    · have offsetLt : square - start % square < square := by omega
      have total : start % square + (square - start % square) = square := by omega
      rw [Nat.mod_mod, Nat.mod_eq_of_lt offsetLt, total, Nat.mod_self]
  constructor
  · intro h
    have eq := Nat.ModEq.add_left_cancel' start
      ((Nat.modEq_zero_iff_dvd.mpr h).trans (Nat.modEq_zero_iff_dvd.mpr divides).symm)
    change i%square = firstMultiple start square % square at eq
    rw [Nat.mod_eq_of_lt below] at eq
    exact ⟨i/square, by simpa only [eq] using (Nat.mod_add_div i square).symm⟩
  · rintro ⟨q, eq⟩
    rw [eq, ← Nat.add_assoc]
    exact dvd_add divides (dvd_mul_right square q)

theorem sieveBandStep_true {lane start last acc p i : ℕ} (lanePos : 0 < lane)
    (pPos : 0 < p) (within : i ≤ last) :
    (sieveBandStep lane start last acc p).testBit (lane*i) = true ↔
      acc.testBit (lane*i) = true ∧ ¬p*p ∣ start+i := by
  let square := p*p
  let offset := firstMultiple start square
  have squarePos : 0 < square := Nat.mul_pos pPos pPos
  change (if offset ≤ last then
    acc ^^^ (acc &&& ((repeatedBits (square*lane) ((last-offset)/square+1)) <<< (lane*offset)))
    else acc).testBit (lane*i) = true ↔
      acc.testBit (lane*i) = true ∧ ¬square ∣ start+i
  by_cases enters : offset ≤ last
  · rw [if_pos enters, Nat.testBit_xor, Nat.testBit_and]
    have repeated :
        ((repeatedBits (square*lane) ((last-offset)/square+1)) <<< (lane*offset)).testBit (lane*i) = true ↔
        square ∣ start+i := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, firstMultiple_iff squarePos,
        testBit_repeatedBits (Nat.mul_pos squarePos lanePos)]
      constructor
      · rintro ⟨ordered, q, _, equation⟩
        have iGe : offset ≤ i := Nat.le_of_mul_le_mul_left ordered lanePos
        have same : lane*(i-offset) = (square*lane)*q := by
          rw [Nat.mul_sub_left_distrib, ← equation]
        have after : i-offset = square*q := Nat.eq_of_mul_eq_mul_left lanePos (by simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using same)
        exact ⟨q, by omega⟩
      · rintro ⟨q, equation⟩
        have iGe : offset ≤ i := by omega
        have after : i-offset = square*q := by omega
        refine ⟨Nat.mul_le_mul_left lane iGe, q, ?_, ?_⟩
        · have subMono : i-offset ≤ last-offset := Nat.sub_le_sub_right within offset
          rw [after] at subMono
          have : q ≤ (last-offset)/square := (Nat.le_div_iff_mul_le squarePos).2 (by
            simpa only [Nat.mul_comm] using subMono)
          omega
        · rw [← Nat.mul_sub_left_distrib, after]
          ac_rfl
    cases a : acc.testBit (lane*i) <;>
      cases b : (((repeatedBits (square*lane) ((last-offset)/square+1)) <<< (lane*offset)).testBit (lane*i)) <;>
      simp_all
  · rw [if_neg enters]
    have clean : ¬square ∣ start+i := by
      rintro h
      obtain ⟨q, eq⟩ := (firstMultiple_iff squarePos).1 h
      change i = offset + square*q at eq
      omega
    simp [clean]

theorem sieveBandFold_true {lane start last i : ℕ} (lanePos : 0 < lane)
    (within : i ≤ last) (ps : List ℕ) (positives : ∀ p ∈ ps, 0 < p) (acc : ℕ) :
    (ps.foldl (sieveBandStep lane start last) acc).testBit (lane*i) = true ↔
      acc.testBit (lane*i) = true ∧ ∀ p ∈ ps, ¬p*p ∣ start+i := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    rw [ih (fun q hq => positives q (List.mem_cons_of_mem _ hq)),
      sieveBandStep_true lanePos (positives p (List.mem_cons_self ..)) within, and_assoc]

def sparseMask (indices : List ℕ) : ℕ :=
  indices.foldl (fun acc j => acc ||| (1 <<< j)) 0

private theorem sparseFold_true (indices : List ℕ) (acc index : ℕ) :
    (indices.foldl (fun n j => n ||| (1 <<< j)) acc).testBit index = true ↔
      acc.testBit index = true ∨ index ∈ indices := by
  induction indices generalizing acc with
  | nil => simp
  | cons i indices ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Bool.or_eq_true]
    simp only [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq, List.mem_cons]
    constructor <;> aesop

theorem sparseMask_true (indices : List ℕ) (index : ℕ) :
    (sparseMask indices).testBit index = true ↔ index ∈ indices := by
  simp [sparseMask, sparseFold_true]

private def rosterWord : ℕ := 0x8820028800000200028020000208800820020220008808028000000a08220008008020208200808000220808220008000a20a00200800220200a00828808228820808a00800200220200028008000020a08808020000800000220808008220008208008220a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac
private def divisorWord : ℕ := 0x20c21c25c20c27c20020c20021420c20022c20c21424c20c20020020c20027420c21c21420c25c2bc20c21421c20c2ac20020c23427c20c2d421420c20020020c21422c20c20023420c27421c20c24c21420c22c20020c21420020c20024420c21c29420c20021420c20021c20c2142ac20c20022c20c24420020c20021420c21c23420c21420020c20021c20c25c20020c27c21420c20020020c2142a420c21c27420c24c22c20c23421420c20020020c21420020c22c20020c20023420c21c21420c24420020c21421c20c27420020c29425c20c20021420c2a420020c21420020c23420020c22c21c20c20021420c2ac20020c21423420c24c2bc20c21c20020c20021420c20021c20c21420020c24420020c20024c20c22c21420c21c20020c21427420c2d421c20c20020020c20021420c20020020c21422c20c21c20020c2bc24420c20021420c22c27c20c21420020c2002a420c23420020c21c21420c20020020c21421c20c20022c20c20020020c20021420c29420020c21420020c20020020c20021c20c20021420c20024420c21420020c20020020c21c22c20c20021420c24c21c20c21420020c22c29420c2ac20020c20021420c21c20020c21424c20c25c21c20c20020020c23421420c27420020c21427c20c21c24420c22c23420c20021420c20020020c21420020c2002ac20c24420020c21c21420c20022c20c21421c20c23425c20c2002a420c22c21420c2bc24c20c21423420c29420020c20021c20c20021420c25c20020c21422c20c27c20020c21c20020c20021420c22c21c20c21420020c2a420020c24c20020c27421420c21c20020c21420020c20021c20c20020020c20021420c20025c20c21424420c21c20020c23420020c20021420c20020020c21420020c24423420c25c22c20c21c21420c20020020c21421c20c22c20020c20027420c20021420c2002ac20c21420020c20020020c27c21c20c29421420c20023420c21420020c20020020c21c25c20c24421420c20021c20c21420020c2bc20020c20027c20c23421420c21c22c20c21429420c20021c20c2a423420c22c21420c20024420c21420020c21c24c20c20020020c20021420c20020020c21422c20c23427420c20020020c21c21420c22c20020c21421c20c20020020c20020020c27c21420c24c20020c21420020c27422c20c20021c20c25c21420c23420020c21424c20c20020020c21c2ac20c20021420c20021c20c21420020c20020020c20022c20c20021420c21c20020c21420020c22c21c20c23429420c24c21420c20020020c21427420c21c23420c20020020c2a421420c24424c20c21420020c25c20020c22c20020c21c21420c27c20020c21421c20c20020020c20020020c20021420c20022c20c21424420c2ac20020c24c21c20c22c21420c20027c20c21420020c24425c20c21c20020c23421420c20021c20c21422c20c20020020c20023420c20021420c21c27420c2142a420c20021c20c20024420c20021420c20029420c21420020c21c22c20c20020020c24421420c27420020c21423420c20020020c20024c20c21c21420c2a425c20c21421c20c20020020c20022c20c20021420c23424420c21427c20c22c20020c25c21c20c20021420c20020020c21420020c20020020c21c20020c20021420c29421c20c21420020c20024c20c22c20020c20021420c21c20020c21420020c20021c20c20025c20c27421420c20022c20c21420020c21c29420c24420020c22c21420c24c20020c21420020c20020020c20020020c21c21420c20023420c21421c20c20027c20c20020020c20021420c22c20020c21420020c20020020c20021c20c23421420c24420020c21425c20c20022c20c21c23420c24c21420c20021c20c21420020c29420020c27420020c25c21420c21c24c20c21424420c23421c20c27c22c20c20021420c20020020c21423420c21c20020c20020020c20021420c20020020c21420020c20020020c24c27c20c21c21420c23420020c21421c20c20027420c22c24420c20021420c20020020c21420020c25c20020c20021c20c24421420c20022c20c21420020c27420020c21c20020c22c21420c20021c20c21420020c24c23420c20020020c27c21420c21c24420c21422c20c20021c20c20024c20c20021420c22c20020c21420020c21c20020c20020020c20021420c25c23420c21427420c20022c20c20020020c21c21420c20020020c21421c20c20024420c20020020c23421420c20020020c21420020c20024c20c24421c20c20021420c20025c20c21420020c22c20020c21c20020c20021420c27c21c20c21420020c23420020c25c20020c20021420c21c20020c21423420c20021c20c22c20020c20021420c24427420c21424c20c21c20020c20020020c20021420c23422c20c21420020c20020020c20025c20c21c21420c27420020c21421c20c20020020c20020020c24c21420c20020020c21422c20c24420020c23421c20c20021420c22c24c20c21420020c20023420c21c20020c20021420c20021c20c21420020c20022c20c20024420c20021420c21c20020c21425c20c20021c20c24c20020c24421420c20023420c21420020c21c20020c20022c20c25c21420c20020020c21420020c22c20020c20020020c21c21420c20024420c21421c20c20020020c20023420c20021420c20020020c21420020c24c20020c22c21c20c20021420c20020020c21420020c23420020c21c24c20c20021420c20021c20c21423420c25c24420c20020020c22c21420c21c20020c21420020c20021c20c24420020c20021420c23420020c21422c20c21c20020c20020020c20021420c22c20020c21420020c20024c20c20020020c21c21420c20020020c21421c20c20022c20c23420020c20021420c24420020c21420020c20023420c20021c20c20021420c24c20020c21420020c20020020c21c22c20c20021420c20021c20c21424420c22c20020c20020020c20021420c21c23420c21420020c24421c20c20020020c20021420c20020020c21420020c21c20020c22c20020c23421420c20020020c21420020c20020020c20023420c21c21420c20022c20c21421c20c20020020c20020020c22c21420c20020020c21420020c23420020c20021c20c20021420c20020020c21422c20c20020020c21c20020c20021420c22c21c20c21420020c20020020c20020020c20021420c21c20020c21420020c20021c20c20020020c20021420c20020020c21420020c21c20020c20020020c20021420c20020020c21420020c20020020c20020020c2002002000000
private def divisorDigit (p : ℕ) : ℕ := (divisorWord >>> (6*p)) % 64

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rosterWord_eq : sparseMask primeRoster = rosterWord := by decide +kernel

private def rosterCondition (p : ℕ) : Bool :=
  decide (p < 2) || (rosterWord.testBit p ||
    (decide (2 ≤ divisorDigit p) && decide (divisorDigit p < p) && decide (p % divisorDigit p = 0)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rosterGate : (List.range 3203).all rosterCondition = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rosterLowerGate : primeRoster.all (fun p => 2 ≤ p) = true := by decide +kernel

theorem roster_contains {p : ℕ} (prime : Nat.Prime p) (bound : p < 3203) : p ∈ primeRoster := by
  have gate := List.all_eq_true.mp rosterGate p (List.mem_range.mpr bound)
  simp only [rosterCondition, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at gate
  rcases gate with smaller | present | ⟨⟨nontrivial, proper⟩, divides⟩
  · exact (Nat.not_lt_of_ge prime.two_le smaller).elim
  · rw [← rosterWord_eq] at present
    exact (sparseMask_true primeRoster p).1 present
  · rcases (Nat.dvd_prime prime).1 ((Nat.dvd_iff_mod_eq_zero).2 divides) with one | same
    · omega
    · omega

theorem roster_lower {p : ℕ} (member : p ∈ primeRoster) : 2 ≤ p :=
  of_decide_eq_true (List.all_eq_true.mp rosterLowerGate p member)

theorem sieveBandFold_nonzero_bit {lane start last index : ℕ} (ps : List ℕ) (acc : ℕ) :
    (ps.foldl (sieveBandStep lane start last) acc).testBit index = true →
      acc.testBit index = true := by
  induction ps generalizing acc with
  | nil => exact id
  | cons p ps ih =>
    rw [List.foldl_cons]
    intro h
    replace h := ih _ h
    by_cases small : firstMultiple start (p*p) ≤ last
    · simp only [sieveBandStep, if_pos small, Nat.testBit_xor, Nat.testBit_and] at h
      cases hb : acc.testBit index <;> simp_all
    · simpa only [sieveBandStep, if_neg small] using h

private theorem initial_true {lane start last index : ℕ} (width : 0 < lane) :
    (if start = 0 then repeatedBits lane (last+1) ^^^ 1 else repeatedBits lane (last+1)).testBit
        index = true ↔ ∃ i ≤ last, 0 < start+i ∧ lane*i = index := by
  by_cases zero : start = 0
  · subst start
    rw [if_pos (rfl : (0 : ℕ) = 0), Nat.testBit_xor]
    simp only [Nat.zero_add]
    by_cases low : index = 0
    · subst index
      have b : (repeatedBits lane (last+1)).testBit 0 = true :=
        (testBit_repeatedBits width _ _).2 ⟨0,by omega,by simp⟩
      rw [b, Nat.testBit_one_zero]
      change false = true ↔ ∃ i ≤ last, 0 < i ∧ lane*i = 0
      constructor
      · intro impossible
        contradiction
      · rintro ⟨i, _, hi, eq⟩
        exact ((Nat.ne_of_gt (Nat.mul_pos width hi)) eq).elim
    · have b : (1 : ℕ).testBit index = false := by
        cases h : (1 : ℕ).testBit index <;> simp_all [Nat.testBit_one_eq_true_iff_self_eq_zero]
      simp only [b, Bool.xor_false, testBit_repeatedBits width]
      constructor
      · rintro ⟨i, bound, eq⟩
        have hi : 0 < i := by
          by_contra! hn
          have : i = 0 := by omega
          exact low (by simpa [this] using eq.symm)
        exact ⟨i,by omega,hi,eq⟩
      · rintro ⟨i, bound, _, eq⟩
        exact ⟨i,by omega,eq⟩
  · simp only [if_neg zero, testBit_repeatedBits width]
    constructor
    · rintro ⟨i, bound, eq⟩
      exact ⟨i,by omega,by omega,eq⟩
    · rintro ⟨i, bound, _, eq⟩
      exact ⟨i,by omega,eq⟩

theorem squarefreeBand_true {lane start last i : ℕ} (width : 0 < lane)
    (absoluteBound : start+last ≤ 10252804) (within : i ≤ last) :
    (squarefreeBand lane start last).testBit (lane*i) = true ↔ Squarefree (start+i) := by
  unfold squarefreeBand
  rw [sieveBandFold_true width within _ (fun _ hm => lt_of_lt_of_le Nat.zero_lt_two (roster_lower hm))]
  rw [initial_true width]
  have localPos :
      (∃ j ≤ last, 0 < start+j ∧ lane*j = lane*i) ↔ 0 < start+i := by
    constructor
    · rintro ⟨j, _, positive, equal⟩
      simpa only [Nat.eq_of_mul_eq_mul_left width equal] using positive
    · intro positive
      exact ⟨i, within, positive, rfl⟩
  rw [localPos]
  constructor
  · rintro ⟨positive, hs⟩
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p prime divides
    have pBound : p < 3203 := by
      by_contra! h
      have huge := Nat.mul_le_mul h h
      have small := Nat.le_of_dvd positive divides
      omega
    exact hs p (roster_contains prime pBound) divides
  · intro sf
    refine ⟨Nat.pos_of_ne_zero sf.ne_zero, ?_⟩
    intro p inRoster divides
    have unit : IsUnit p := sf p divides
    have e : p = 1 := Nat.isUnit_iff.mp unit
    have h := roster_lower inRoster
    omega

theorem squarefreeBand_support {lane start last index : ℕ} (width : 0 < lane) :
    (squarefreeBand lane start last).testBit index = true →
      ∃ i ≤ last, 0 < start+i ∧ lane*i = index := by
  intro h
  exact (initial_true width).1 (sieveBandFold_nonzero_bit primeRoster _ h)


open OMA.PackedConvolution

theorem squarefreeBand_pack {lane start last : ℕ} (width : 0 < lane)
    (absoluteBound : start+last ≤ 10252804) :
    squarefreeBand lane start last =
      pack (2^lane) (last+1) (fun i => squarefreeDigit (start+i)) := by
  have large : 1 < 2^lane := Nat.one_lt_two_pow width.ne'
  have bound (i : ℕ) (_ : i < last+1) : squarefreeDigit (start+i) < 2^lane := by
    unfold squarefreeDigit
    split <;> omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [pack_testBit lane (last+1) _ width bound]
  have address : j%lane+lane*(j/lane)=j := Nat.mod_add_div j lane
  have forced (present : (squarefreeBand lane start last).testBit j = true) :
      j/lane < last+1 ∧ j%lane = 0 := by
    obtain ⟨i, hi, _, maskIndex⟩ := squarefreeBand_support width present
    rw [← maskIndex, Nat.mul_div_cancel_left _ width, Nat.mul_mod_right]
    exact ⟨by omega,rfl⟩
  by_cases inside : j/lane < last+1
  · rw [if_pos inside]
    by_cases aligned : j%lane = 0
    · rw [aligned]
      have physical : lane*(j/lane)=j := by simpa [aligned] using address
      have coord := squarefreeBand_true width absoluteBound (show j/lane ≤ last by omega)
      rw [physical] at coord
      apply Bool.eq_iff_iff.mpr
      rw [coord]
      by_cases sf : Squarefree (start+j/lane) <;> simp [squarefreeDigit, sf]
    · have none : (squarefreeBand lane start last).testBit j = false := by
        cases h : (squarefreeBand lane start last).testBit j
        · rfl
        · exact (aligned (forced h).2).elim
      rw [none]
      unfold squarefreeDigit
      split
      · cases h : (1:ℕ).testBit (j%lane)
        · rfl
        · exact (aligned (Nat.testBit_one_eq_true_iff_self_eq_zero.1 h)).elim
      · simp
  · rw [if_neg inside]
    cases h : (squarefreeBand lane start last).testBit j
    · rfl
    · exact (inside (forced h).1).elim

end OMA.SquarefreeRepresentation

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

namespace OMA.SquarefreeRepresentation

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

theorem spread_pack (lane bits count : ℕ) (f : ℕ → ℕ) (hlane : 0<lane) (hcount : count≤2^bits)
    (hf : ∀ i < count, f i < 2) :
    spread lane bits (pack 2 count f) = pack (2^lane) count f := by
  let source := pack 2 count f
  have small : source < 2^count := pack_lt_pow f hf
  rw [spread_eq_pack _ _ _ hlane (small.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hcount))]
  change pack (2^lane) (2^bits) (fun i => source / 2^i % 2) = _
  change (∑ i ∈ range (2^bits), (source / 2^i % 2)*(2^lane)^i) = ∑ i ∈ range count, f i*(2^lane)^i
  calc
    _ = ∑ i ∈ range count, (source / 2^i % 2)*(2^lane)^i := by
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr hcount)
      intro i _ out
      have above : count ≤ i := by simpa [Finset.mem_range] using out
      have hz : source/2^i = 0 := Nat.div_eq_of_lt
        (small.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) above))
      simp [hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hin
      rw [show source/2^i%2=f i from digit_pack f (by decide) hf (Finset.mem_range.mp hin)]

end OMA.SquarefreeRepresentation

namespace OMA.SquarefreeRepresentation

open Finset OMA.PackedConvolution

theorem expandedSquarefreeBand {lane start last : ℕ} (width : 0 < lane)
    (absolute : start+last ≤ 10252804) :
    spread lane (Nat.log2 last+1) (squarefreeBand 1 start last) = squarefreeBand lane start last := by
  let f := fun i => squarefreeDigit (start+i)
  have binary : squarefreeBand 1 start last = pack 2 (last+1) f :=
    squarefreeBand_pack (by decide) absolute
  have expanded : squarefreeBand lane start last = pack (2^lane) (last+1) f :=
    squarefreeBand_pack width absolute
  have size : last+1 ≤ 2^(Nat.log2 last+1) := Nat.succ_le_of_lt Nat.lt_log2_self
  have digit (i : ℕ) (_ : i < last+1) : f i < 2 := by
    unfold f squarefreeDigit
    split <;> decide
  rw [binary, spread_pack lane (Nat.log2 last+1) (last+1) f width size digit, ← expanded]

end OMA.SquarefreeRepresentation

namespace OMA.SquarefreeRepresentation

open Finset OMA.PackedConvolution

def squarefreeMask (lane last : ℕ) : ℕ :=
  spread lane (Nat.log2 last+1) (squarefreeBand 1 0 last)

def squaresMask (lane count : ℕ) : ℕ :=
  (List.range count).foldl (fun acc i => acc ||| (1 <<< (lane * (i + 1)^2))) 0

def cutoff : ℕ := 187425
def lowLane : ℕ := 18
def lowOnes : ℕ := repeatedBits lowLane (cutoff + 1)
def lowCoefficients : ℕ := squarefreeMask lowLane cutoff * squaresMask lowLane 432

def lowThreshold (value : ℕ) : ℕ :=
  let highShift := lowLane - 1
  let positions := (lowOnes - 1) <<< highShift
  (lowCoefficients + ((1 <<< highShift) - value) * lowOnes) &&& positions

def lowLevel (value : ℕ) : ℕ :=
  ((lowThreshold value) ^^^ (lowThreshold (value + 1))) >>> (lowLane - 1)

def lowCounts : List ℕ :=
  (List.range 101).map fun value => lowLevel value % ((1 <<< lowLane) - 1)

def expectedCounts : List ℕ := [2, 9, 19, 27, 38, 36, 57, 63, 62, 74, 94, 86, 101, 112, 123, 113, 139, 140, 146, 170, 155, 202, 167, 196, 204, 213, 213, 215, 233, 232, 255, 249, 276, 261, 278, 310, 321, 300, 302, 336, 347, 325, 325, 350, 375, 367, 413, 393, 377, 384, 427, 435, 440, 447, 434, 472, 445, 476, 470, 518, 482, 499, 510, 542, 519, 550, 506, 553, 591, 572, 626, 586, 582, 585, 598, 623, 623, 656, 595, 697, 641, 672, 702, 689, 733, 696, 661, 718, 738, 757, 755, 739, 820, 734, 717, 834, 792, 811, 780, 831, 867]
def expectedLast : List ℕ := [13, 61, 85, 196, 225, 441, 621, 909, 1089, 1125, 1521, 2025, 2700, 2200, 2925, 3969, 3825, 4500, 5625, 4869, 6084, 8100, 11025, 7425, 9900, 9981, 10584, 11925, 12825, 14400, 13500, 14625, 18081, 18225, 17424, 20925, 22500, 27225, 21825, 25425, 27000, 28224, 27900, 38025, 44100, 33300, 35721, 35325, 39825, 37044, 39600, 40725, 44325, 55125, 50625, 53100, 52200, 54000, 60300, 65025, 63900, 60025, 63504, 64125, 74529, 81225, 77400, 99225, 88200, 76500, 79200, 87525, 90000, 108900, 88425, 91800, 95400, 96300, 100125, 107325, 132300]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem allCounts :
    (List.range 101).all (fun value =>
      lowLevel value % ((1 <<< lowLane) - 1) == expectedCounts[value]!) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem allEndpoints :
    (List.range 81).all (fun value =>
      let mask := lowLevel value
      let endpoint := expectedLast[value]!
      mask.testBit (lowLane * endpoint) && (mask >>> (lowLane * (endpoint + 1)) == 0)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem zeros : lowLevel 0 = (1 <<< lowLane) + (1 <<< (13 * lowLane)) := by
  decide +kernel

end OMA.SquarefreeRepresentation

namespace OMA.SquarefreeRepresentation

open Finset OMA.PackedConvolution

private theorem power_square_fold (lane : ℕ) (positive : 0 < lane) (n : ℕ) :
    squaresMask lane n = ∑ i ∈ range n, (2^lane)^((i+1)^2) ∧
    squaresMask lane n < 2^(lane*((n+1)^2)) := by
  induction n with
  | zero => simp [squaresMask]
  | succ n ih =>
    have step : squaresMask lane (n+1) = squaresMask lane n + 2^(lane*((n+1)^2)) := by
      unfold squaresMask
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.or_two_pow_eq_add_of_lt ih.2
    constructor
    · rw [step, Finset.sum_range_succ, ih.1, Nat.pow_mul]
    · rw [step]
      calc
        _ < 2^(lane*((n+1)^2)) + 2^(lane*((n+1)^2)) := Nat.add_lt_add_right ih.2 _
        _ = 2^(lane*((n+1)^2)+1) := by rw [pow_succ]; omega
        _ ≤ 2^(lane*((n+1+1)^2)) := by
          have sq : (n+1)^2 < (n+1+1)^2 := Nat.pow_lt_pow_left (by omega) (by decide)
          have monotone := Nat.mul_lt_mul_of_pos_left sq positive
          exact Nat.pow_le_pow_right (by decide) (by omega)

theorem squaresMask_sum (lane n : ℕ) (positive : 0 < lane) :
    squaresMask lane n = ∑ k ∈ Icc 1 n, (2^lane)^(k^2) := by
  rw [(power_square_fold lane positive n).1]
  refine sum_bij (fun i _ => i+1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    simp only [mem_range] at hi
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ e
    omega
  · intro i hi
    obtain ⟨lo,hi⟩ := mem_Icc.mp hi
    exact ⟨i-1, mem_range.mpr (by omega), by omega⟩

private theorem lowOnes_pack : lowOnes = repeated 17 187426 1 := by
  change ((1 <<< (18*187426))-1) / ((1 <<< 18)-1) = repeated 17 187426 1
  simp only [Nat.shiftLeft_eq, Nat.one_mul, repeated]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem lowIntervalData
    (hsf : squarefreeMask lowLane cutoff = pack (2^18) 187426 squarefreeDigit) :
    let T := fun j => (Icc 1 187425).filter
      (fun n => OMA.S_oeis_a085264.representations n = j)
    T 0 = {1,13} ∧
    (∀ i : Fin OMA.S_oeis_a085264.lastTable.length,
      IsGreatest (T i.val : Set ℕ) (OMA.S_oeis_a085264.lastTable.get i)) ∧
    (∀ i : Fin OMA.S_oeis_a085264.frequencyTable.length,
      (T i.val).card = OMA.S_oeis_a085264.frequencyTable.get i) := by
  have hs : squaresMask lowLane 432 = ∑ k ∈ Icc 1 432, (2^18)^(k^2) := by
    simpa only [lowLane] using squaresMask_sum lowLane 432 (by decide)
  have hc := low_coefficients_of_product (coefficients := lowCoefficients)
    (show lowCoefficients = squarefreeMask lowLane cutoff * squaresMask lowLane 432 from rfl) hsf hs
  have counts : (List.range 101).all (fun value =>
      positiveLowLevel lowCoefficients lowOnes value % ((2^18)-1) ==
        OMA.S_oeis_a085264.frequencyTable[value]!) = true := allCounts
  have lasts : (List.range OMA.S_oeis_a085264.lastTable.length).all (fun value =>
      let mask := positiveLowLevel lowCoefficients lowOnes value
      let endpoint := OMA.S_oeis_a085264.lastTable[value]!
      mask.testBit (18 * endpoint) && (mask >>> (18 * (endpoint + 1)) == 0)) =
      true := allEndpoints
  have freqLength : OMA.S_oeis_a085264.frequencyTable.length ≤ 101 := by decide
  have lastLength : OMA.S_oeis_a085264.lastTable.length ≤ 101 := by decide
  have goodLast : ∀ i : Fin OMA.S_oeis_a085264.lastTable.length,
      OMA.S_oeis_a085264.lastTable.get i < 187426 := by decide +kernel
  have hz : positiveLowLevel lowCoefficients lowOnes 0 = (1 <<< 18) + (1 <<< (13*18)) := zeros
  have fz : OMA.S_oeis_a085264.frequencyTable[0]! = 2 := by decide
  change lowFinset 0 = {1,13} ∧
    (∀ i : Fin OMA.S_oeis_a085264.lastTable.length,
      IsGreatest (lowFinset i.val : Set ℕ) (OMA.S_oeis_a085264.lastTable.get i)) ∧
    (∀ i : Fin OMA.S_oeis_a085264.frequencyTable.length,
      (lowFinset i.val).card = OMA.S_oeis_a085264.frequencyTable.get i)
  exact low_data_from_gates lowCoefficients lowOnes hc lowOnes_pack
    OMA.S_oeis_a085264.frequencyTable OMA.S_oeis_a085264.lastTable
    freqLength lastLength goodLast counts lasts hz fz

end OMA.SquarefreeRepresentation

namespace OMA.SquarefreeRepresentation

open Finset OMA.PackedConvolution OMA.S_oeis_a085264

theorem finiteIntervalData
    (hsf : squarefreeMask lowLane cutoff = pack (2^18) 187426 squarefreeDigit)
    (tail : ∀ n : ℕ, 187425 < n → n ≤ 10252804 → 100 < representations n) :
    let T := fun j => (Icc 1 10252804).filter (fun n => representations n = j)
    T 0 = {1,13} ∧
    (∀ i : Fin lastTable.length, IsGreatest (T i.val : Set ℕ) (lastTable.get i)) ∧
    (∀ i : Fin frequencyTable.length, (T i.val).card = frequencyTable.get i) := by
  let T := fun j => (Icc 1 10252804).filter (fun n => representations n = j)
  have low (j : ℕ) (hj : j≤100) : T j = lowFinset j := by
    ext n
    change n ∈ (Icc 1 10252804).filter (fun n => representations n = j) ↔
      n ∈ (Icc 1 187425).filter (fun n => representations n = j)
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hp,hu⟩,he⟩
      have h := fun hn => tail n hn hu
      exact ⟨⟨hp,by omega⟩,he⟩
    · rintro ⟨⟨hp,hu⟩,he⟩
      exact ⟨⟨hp,by omega⟩,he⟩
  obtain ⟨hzero, hlast, hfreq⟩ := lowIntervalData hsf
  change lowFinset 0 = {1,13} at hzero
  change (∀ i : Fin lastTable.length, IsGreatest (lowFinset i.val : Set ℕ) (lastTable.get i)) at hlast
  change (∀ i : Fin frequencyTable.length, (lowFinset i.val).card = frequencyTable.get i) at hfreq
  change T 0 = {1,13} ∧ _ ∧ _
  refine ⟨(low 0 (by decide)).trans hzero, ?_, ?_⟩
  · intro i
    have hi : i.val < 81 := i.isLt
    change IsGreatest (T i.val : Set ℕ) (lastTable.get i)
    rw [low i.val (by omega)]
    exact hlast i
  · intro i
    have hi : i.val < 101 := i.isLt
    change (T i.val).card = frequencyTable.get i
    rw [low i.val (by omega)]
    exact hfreq i

end OMA.SquarefreeRepresentation

namespace OMA.SquarefreeRepresentation

open Finset OMA.PackedConvolution

theorem repeatedBits_quotient {width : ℕ} (positive : 0 < width) (count : ℕ) :
    repeatedBits width count = (2^(width*count)-1)/(2^width-1) := by
  rw [repeatedBits_eq_sum positive]
  simpa only [Nat.pow_mul] using Nat.geomSum_eq (Nat.one_lt_two_pow (Nat.ne_of_gt positive)) count

def thresholdWindowGate (width cap level first last mask : ℕ) : Prop :=
  let lane := width+1
  let start := first - cap^2
  let offset := first - start
  let count := last + 1 - first
  let all := repeatedBits lane count
  let coefficients := mask * squaresMask lane cap
  let window := (coefficients >>> (lane * offset)) % (1 <<< (lane * count))
  ((window + (2^width-level) * all) &&& (2^width * all)) = 2^width * all

theorem thresholdWindow_sound {width cap level first last mask : ℕ}
    (capSmall : cap+(2^width-level) < 2^(width+1)) (levelSmall : level ≤ 2^width)
    (ordered : first ≤ last) (absolute : last ≤ 10252804)
    (input : mask = squarefreeBand (width+1) (first-cap^2) (last-(first-cap^2)))
    (checked : thresholdWindowGate width cap level first last mask) :
    ∀ q, first ≤ q → q ≤ last → level ≤ representationCount q := by
  let start := first-cap^2
  let offset := first-start
  let count := last+1-first
  let m := last-start+1
  let n := cap^2+1
  have startLt : start ≤ first := Nat.sub_le _ _
  have startEnd : start ≤ last := startLt.trans ordered
  have bound : start+(last-start) ≤ 10252804 := by omega
  have positive : 0 < width+1 := Nat.succ_pos width
  have exactInput : mask = pack (2^(width+1)) m (fun i => squarefreeDigit (start+i)) :=
    input.trans (squarefreeBand_pack positive bound)
  have exactFactor : squaresMask (width+1) cap = pack (2^(width+1)) n (truncatedSquareDigit cap) :=
    (squaresMask_sum (width+1) cap positive).trans
      (pack_truncated_squares (2^(width+1)) cap n (by simp [n])).symm
  have range : offset+count ≤ m+n := by
    dsimp [offset,count,m]
    omega
  have checked' :
      thresholdBits
        ((pack (2^(width+1)) m (fun i => squarefreeDigit (start+i)) *
            pack (2^(width+1)) n (truncatedSquareDigit cap)) /
          (2^(width+1))^offset % (2^(width+1))^count)
        (repeated width count (2^width-level)) (repeated width count (2^width)) =
          repeated width count (2^width) := by
    rw [← exactInput, ← exactFactor]
    unfold thresholdBits repeated
    have gate := checked
    dsimp only [thresholdWindowGate] at gate
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul,
      repeatedBits_quotient positive] at gate
    simpa only [Nat.pow_mul] using gate
  have good := representation_lower_window_padded capSmall levelSmall range checked'
  intro q lo hi
  have idx : q-first < count := by dsimp [count]; omega
  have pass := good (q-first) idx
  have equal : start+offset+(q-first) = q := by dsimp [offset]; omega
  exact equal ▸ pass

def tailWindowGate (first last mask : ℕ) : Prop :=
  thresholdWindowGate 9 512 101 first last mask

theorem tailWindow_sound {first last mask : ℕ} (ordered : first ≤ last)
    (absolute : last ≤ 10252804)
    (input : mask = squarefreeBand 10 (first-512^2) (last-(first-512^2)))
    (checked : tailWindowGate first last mask) :
    ∀ n, first ≤ n → n ≤ last → 101 ≤ representationCount n :=
  thresholdWindow_sound (width := 9) (cap := 512) (level := 101)
    (by decide) (by decide) ordered absolute input checked

def bandMask (first last : ℕ) : Prop :=
  let lane := 10
  let start := first - 512^2
  let lastIndex := last - start
  let firstIndex := first - start
  let count := last + 1 - first
  let all := repeatedBits lane count
  let coefficients := spread lane (Nat.log2 lastIndex+1) (squarefreeBand 1 start lastIndex) * squaresMask lane 512
  let window := (coefficients >>> (lane * firstIndex)) % (1 <<< (lane * count))
  ((window + 411 * all) &&& (512 * all)) = 512 * all

instance (first last : ℕ) : Decidable (bandMask first last) := by unfold bandMask; infer_instance

def firstOfBand (index : ℕ) : ℕ := 187426 + 786432 * index
def lastOfBand (index : ℕ) : ℕ := min 10252804 (firstOfBand index + 786431)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def bandCertificate : PLift ((List.range 13).all (fun index => decide (bandMask (firstOfBand index) (lastOfBand index))) = true) := ⟨by decide +kernel⟩

theorem allBands : (List.range 13).all (fun index => decide (bandMask (firstOfBand index) (lastOfBand index))) = true := bandCertificate.down

private theorem bandMask_window (first last : ℕ) :
    bandMask first last ↔
      tailWindowGate first last
        (spread 10 (Nat.log2 (last-(first-512^2))+1)
          (squarefreeBand 1 (first-512^2) (last-(first-512^2)))) :=
  Iff.rfl

theorem highIntervalData
    (expandCorrect : ∀ first last : ℕ, first ≤ last → last ≤ 10252804 →
      let start := first-512^2
      let lastIndex := last-start
      spread 10 (Nat.log2 lastIndex+1) (squarefreeBand 1 start lastIndex) =
        squarefreeBand 10 start lastIndex)
    (checked : (List.range 13).all
      (fun index => decide (bandMask (firstOfBand index) (lastOfBand index))) = true) :
    ∀ n, 187425 < n → n ≤ 10252804 → 100 < representationCount n := by
  intro n lower upper
  let index := (n-187426)/786432
  have indexBound : index < 13 := by
    dsimp only [index]
    omega
  have decomposition : (n-187426)%786432 + 786432*index = n-187426 :=
    Nat.mod_add_div (n-187426) 786432
  have remainder : (n-187426)%786432 < 786432 := Nat.mod_lt _ (by decide)
  have firstBound : firstOfBand index ≤ n := by
    unfold firstOfBand
    omega
  have lastBound : n ≤ lastOfBand index := by
    unfold lastOfBand
    refine le_min upper ?_
    unfold firstOfBand
    omega
  have ordered := firstBound.trans lastBound
  have absolute : lastOfBand index ≤ 10252804 := min_le_left _ _
  have band := of_decide_eq_true
    (List.all_eq_true.mp checked index (List.mem_range.mpr indexBound))
  exact tailWindow_sound ordered absolute
    (expandCorrect (firstOfBand index) (lastOfBand index) ordered absolute)
    ((bandMask_window _ _).mp band) n firstBound lastBound

theorem expandedWindow (first last : ℕ) (ordered : first ≤ last) (absolute : last ≤ 10252804) :
    let start := first-512^2
    let lastIndex := last-start
    spread 10 (Nat.log2 lastIndex+1) (squarefreeBand 1 start lastIndex) =
      squarefreeBand 10 start lastIndex := by
  dsimp only
  apply expandedSquarefreeBand (by decide : 0 < 10)
  have bound : first-512^2 ≤ last := (Nat.sub_le _ _).trans ordered
  omega

theorem lowInputExact : squarefreeMask lowLane cutoff = pack (2^18) 187426 squarefreeDigit := by
  have shift : (fun i => squarefreeDigit (0+i)) = squarefreeDigit :=
    funext (fun i => congrArg squarefreeDigit (Nat.zero_add i))
  have expand := expandedSquarefreeBand (lane:=18) (start:=0) (last:=187425) (by decide) (by decide)
  have packed := squarefreeBand_pack (lane:=18) (start:=0) (last:=187425) (by decide) (by decide)
  exact expand.trans (packed.trans (congrArg (pack (2^18) 187426) shift))

theorem tailRangeExact :
    ∀ n : ℕ, 187425 < n → n ≤ 10252804 → 100 < OMA.S_oeis_a085264.representations n :=
  highIntervalData expandedWindow allBands

end OMA.SquarefreeRepresentation

theorem OMA.solution : OMA.R_oeis_a085264_R1.H3 :=
  OMA.SquarefreeRepresentation.finiteIntervalData OMA.SquarefreeRepresentation.lowInputExact OMA.SquarefreeRepresentation.tailRangeExact