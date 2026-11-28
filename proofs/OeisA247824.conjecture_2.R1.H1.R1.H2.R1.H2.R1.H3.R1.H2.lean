import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H3_R1
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Count
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Card

/- The complete-block sieve uses the finite Legendre sum of @physbuzz, credited in the parent to Daniel Veljjanoski and @rleshner (PR #9315). The segmented sieve and certificates are from @Medrov. -/

namespace Astra247824
open Finset OMA.R_OeisA247824_conjecture_2_R1_H1_R1
def sieveStep (p : ℕ) (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  if x < p then (if x = 0 then 0 else 1) else f x - f (x / p)

def phi (p : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | a+1 => sieveStep (p a) (phi p a)

theorem phi_eq_fold (p : ℕ → ℕ) (a : ℕ) :
    phi p a = ((List.range a).map p).reverse.foldr sieveStep id := by
  induction a with
  | zero => rfl
  | succ a ih => simp [phi, List.range_succ, ih]

def rough (y x : ℕ) : ℕ :=
  ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card

theorem rough_eq_phi (p : ℕ → ℕ) (a y x : ℕ)
    (primeList : (List.range a).map p =
      (List.range (y+1)).filter (fun q => decide q.Prime)) :
    rough y x = phi p a x := by
  rw [phi_eq_fold, primeList]
  exact (legendre_range y x).symm

theorem rough_succ (y x : ℕ) :
    rough y (x+1) = rough y x + (if ∀ p ∈ Nat.primesLE y, ¬ p ∣ x+1 then 1 else 0) := by
  unfold rough
  have interval : insert (x+1) (Icc 1 x) = Icc 1 (x+1) :=
    insert_Icc_right_eq_Icc_succ (by omega : 1 ≤ x+1)
  rw [← interval, filter_insert]
  have fresh : x+1 ∉ (Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n) := by simp
  split <;> simp_all

theorem rough_period {w y : ℕ} (hw : ∀ p ∈ Nat.primesLE y, p ∣ w) (x : ℕ) :
    rough y (w+x) = rough y w + rough y x := by
  induction x with
  | zero => simp [rough]
  | succ x ih =>
    have equiv : (∀ p ∈ Nat.primesLE y, ¬ p ∣ w + (x+1)) ↔
        (∀ p ∈ Nat.primesLE y, ¬ p ∣ x+1) := by
      constructor
      · exact fun h p hp hd => h p hp ((Nat.dvd_add_iff_right (hw p hp)).mp hd)
      · exact fun h p hp hd => h p hp ((Nat.dvd_add_iff_right (hw p hp)).mpr hd)
    rw [← Nat.add_assoc, rough_succ y (w+x), ih, rough_succ y x, Nat.add_assoc w x 1]
    by_cases h : ∀ p ∈ Nat.primesLE y, ¬ p ∣ x+1
    · simp only [if_pos h, if_pos (equiv.mpr h), Nat.add_assoc]
    · simp only [if_neg h, if_neg (mt equiv.mp h), Nat.add_assoc]

theorem rough_wheel {w y : ℕ} (hw : ∀ p ∈ Nat.primesLE y, p ∣ w) (x : ℕ) :
    rough y x = (x/w) * rough y w + rough y (x%w) := by
  have periods (k r : ℕ) : rough y (w*k+r) = k * rough y w + rough y r := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Nat.add_right_comm, Nat.add_comm (w*k+r), rough_period hw, ih,
        Nat.succ_mul]
      omega
  calc
    rough y x = rough y (w*(x/w)+x%w) := congrArg (rough y) (Nat.div_add_mod x w).symm
    _ = _ := periods _ _

def multiplesMask (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => 2^p * multiplesMask p k + 1

theorem multiplesMask_fast {p : ℕ} (hp : 0 < p) (k : ℕ) :
    multiplesMask p k = (2^(p*k)-1)/(2^p-1) := by
  have gt : 1 < (2:ℕ)^p := Nat.one_lt_pow (by omega) (by decide)
  have d : 2^p-1+1 = (2:ℕ)^p := by omega
  have mul (n : ℕ) : multiplesMask p n * (2^p-1) + 1 = (2^p)^n := by
    induction n with
    | zero => simp [multiplesMask]
    | succ n ih =>
      rw [multiplesMask, pow_succ, ← ih]
      calc
        _ = 2^p * multiplesMask p n * (2^p-1) + ((2^p-1)+1) := by ring
        _ = _ := by rw [d]; ring
  have e : multiplesMask p k * (2^p-1) = 2^(p*k)-1 := by
    rw [pow_mul]; have := mul k; omega
  rw [← e, Nat.mul_div_cancel _ (by omega)]

theorem multiplesMask_spec {p : ℕ} (hp : 0 < p) (k i : ℕ) :
    (multiplesMask p k).testBit i = true ↔ ∃ j < k, i = p*j := by
  induction k generalizing i with
  | zero => simp [multiplesMask]
  | succ k ih =>
    have gt : 1 < (2:ℕ)^p := Nat.one_lt_pow (by omega) (by decide)
    rw [multiplesMask, Nat.testBit_two_pow_mul_add _ gt]
    by_cases low : i < p
    · simp only [low, if_true]
      have one : (1:ℕ).testBit i = true ↔ i = 0 := by
        cases i <;> simp [Nat.testBit_succ]
      rw [one]
      constructor
      · rintro rfl; exact ⟨0, by omega, (Nat.mul_zero p).symm⟩
      · rintro ⟨j, _, rfl⟩
        cases j with
        | zero => simp
        | succ j => rw [Nat.mul_succ] at low; omega
    · simp only [low, if_false, ih]
      constructor
      · rintro ⟨j,hj,he⟩
        refine ⟨j+1, by omega, ?_⟩
        rw [Nat.mul_succ]; omega
      · rintro ⟨j,hj,he⟩
        cases j with
        | zero => simp only [Nat.mul_zero] at he; omega
        | succ j =>
          refine ⟨j, by omega, ?_⟩
          rw [Nat.mul_succ] at he; omega

def packedDivisors (p lo width : ℕ) : ℕ :=
  ((2^(p*((lo%p+width)/p+1))-1)/(2^p-1)) >>> (lo%p)

theorem packedDivisors_spec {p lo width i : ℕ} (hp : 0 < p) (hi : i < width) :
    (packedDivisors p lo width).testBit i = true ↔ p ∣ lo+i := by
  unfold packedDivisors
  rw [Nat.testBit_shiftRight, ← multiplesMask_fast hp, multiplesMask_spec hp]
  have moved : p ∣ lo%p+i ↔ p ∣ lo+i := by
    have h : p ∣ p*(lo/p) := ⟨_,rfl⟩
    calc
      p ∣ lo%p+i ↔ p ∣ p*(lo/p)+(lo%p+i) := Nat.dvd_add_iff_right h
      _ ↔ p ∣ lo+i := by rw [← Nat.add_assoc, Nat.div_add_mod]
  rw [← moved]
  constructor
  · rintro ⟨j,_,he⟩; exact ⟨j,he⟩
  · rintro ⟨j,he⟩
    refine ⟨j, Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp).mpr ?_), he⟩
    rw [Nat.mul_comm, ← he]; omega

def clearDivisors (mask p lo width : ℕ) : ℕ :=
  mask ^^^ (mask &&& packedDivisors p lo width)

theorem clearDivisors_spec {mask p lo width i : ℕ} (hp : 0 < p) (hi : i < width) :
    (clearDivisors mask p lo width).testBit i = true ↔ mask.testBit i = true ∧ ¬ p ∣ lo+i := by
  have cutoff := packedDivisors_spec (lo:=lo) hp hi
  unfold clearDivisors
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases hm : mask.testBit i <;> cases hb : (packedDivisors p lo width).testBit i <;> simp_all

def blockMask (lo width : ℕ) : List ℕ → ℕ
  | [] => 2^width-1
  | p::ps => clearDivisors (blockMask lo width ps) p lo width

theorem blockMask_spec {ps : List ℕ} {lo width i : ℕ} (hi : i < width)
    (positive : ∀ p ∈ ps, 0 < p) :
    (blockMask lo width ps).testBit i = true ↔ ∀ p ∈ ps, ¬ p ∣ lo+i := by
  induction ps with
  | nil => simp [blockMask, Nat.testBit_two_pow_sub_one, hi]
  | cons p ps ih =>
    rw [blockMask, clearDivisors_spec (positive p (by simp)) hi,
      ih (fun q hq => positive q (List.mem_cons_of_mem p hq))]
    simp only [List.forall_mem_cons, and_comm]

theorem spaced_bits_mod (stride : ℕ) (S : Finset ℕ) (hs : 0 < stride)
    (limit : S.card < 2^stride-1) :
    (∑ i ∈ S, 2^(stride*i)) % (2^stride-1) = S.card := by
  have gt : 1 < (2:ℕ)^stride := Nat.one_lt_pow (by omega) (by decide)
  have hb : 2^stride ≡ 1 [MOD 2^stride-1] := by
    change 2^stride % (2^stride-1) = 1 % (2^stride-1)
    conv_lhs => arg 1; rw [show 2^stride = 1+(2^stride-1) by omega]
    exact Nat.add_mod_right _ _
  have sum : (∑ i ∈ S, 2^(stride*i)) ≡ ∑ _ ∈ S, 1 [MOD 2^stride-1] := by
    apply Nat.ModEq.sum
    intro i _
    simpa [pow_mul] using hb.pow i
  simpa [Nat.ModEq, Nat.mod_eq_of_lt limit] using sum

theorem mod_of_spaced_support {mask stride : ℕ} (S : Finset ℕ) (hs : 0 < stride)
    (limit : S.card < 2^stride-1)
    (bits : ∀ j, mask.testBit j = true ↔ ∃ i ∈ S, j = stride*i) :
    mask % (2^stride-1) = S.card := by
  have support : mask.bitIndices.toFinset = S.image (fun i => stride*i) := by
    ext j
    simp only [List.mem_toFinset, Nat.mem_bitIndices, Finset.mem_image]
    simpa only [eq_comm] using bits j
  have value : (∑ i ∈ S, 2^(stride*i)) = mask := by
    rw [← Finset.sum_toFinset_bitIndices_two_pow mask, support, Finset.sum_image]
    exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hs h
  rw [← value, spaced_bits_mod stride S hs limit]

def denseLane (stride k r n : ℕ) : ℕ :=
  ((n >>> r) &&& ((2^(stride*k)-1)/(2^stride-1))) % (2^stride-1)

theorem denseLane_spec {stride k : ℕ} (hs : 0 < stride) (room : k < 2^stride-1) (r n : ℕ) :
    denseLane stride k r n = ((range k).filter (fun i => n.testBit (stride*i+r) = true)).card := by
  unfold denseLane
  apply mod_of_spaced_support _ hs
  · exact (card_filter_le ..).trans_lt (by simpa using room)
  · intro j
    rw [Nat.testBit_and, Nat.testBit_shiftRight, ← multiplesMask_fast hs k]
    simp only [Bool.and_eq_true, multiplesMask_spec hs, mem_filter, mem_range]
    constructor
    · rintro ⟨flag,i,hi,rfl⟩
      exact ⟨i, ⟨hi, by simpa [Nat.add_comm] using flag⟩, rfl⟩
    · rintro ⟨i,⟨hi,flag⟩,rfl⟩
      exact ⟨by simpa [Nat.add_comm] using flag, i, hi, rfl⟩

theorem ranks_after_clear {mask p lo width r k : ℕ} (hp : 0 < p) (hr : r < p)
    (aligned : p ∣ lo+r) (cover : width ≤ p*k) (room : k < 2^p-1) :
    ((range width).filter (fun i => mask.testBit i = true)).card =
      ((range width).filter (fun i => (clearDivisors mask p lo width).testBit i = true)).card +
      denseLane p k r (mask % 2^width) := by
  let S := (range width).filter (fun i => mask.testBit i = true)
  have split := card_filter_add_card_filter_not (s:=S) (fun i => p ∣ lo+i)
  have keep : S.filter (fun i => ¬ p ∣ lo+i) =
      (range width).filter (fun i => (clearDivisors mask p lo width).testBit i = true) := by
    ext i
    simp only [S, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨hi,flag⟩,fresh⟩
      exact ⟨hi,(clearDivisors_spec hp hi).mpr ⟨flag,fresh⟩⟩
    · rintro ⟨hi,survives⟩
      obtain ⟨flag,fresh⟩ := (clearDivisors_spec hp hi).mp survives
      exact ⟨⟨hi,flag⟩,fresh⟩
  have remove : denseLane p k r (mask % 2^width) = (S.filter (fun i => p ∣ lo+i)).card := by
    rw [denseLane_spec hp room]
    apply card_bij (fun j _ => p*j+r)
    · intro j hj
      obtain ⟨_,flag⟩ := mem_filter.mp hj
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at flag
      have multiple : p ∣ p*j := ⟨j,rfl⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr flag.1,flag.2⟩,
        by simpa only [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using dvd_add aligned multiple⟩
    · intro i _ j _ h
      exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_right_cancel h)
    · intro i hi
      obtain ⟨inside,div⟩ := mem_filter.mp hi
      obtain ⟨idx,flag⟩ := mem_filter.mp inside
      have bound := mem_range.mp idx
      have congr : lo+i ≡ lo+r [MOD p] := (Nat.mod_eq_zero_of_dvd div).trans (Nat.mod_eq_zero_of_dvd aligned).symm
      have residue : i%p = r%p := Nat.ModEq.add_left_cancel' lo congr
      rw [Nat.mod_eq_of_lt hr] at residue
      have reconstruct : p*(i/p)+r = i := by rw [← residue, Nat.div_add_mod]
      have valid : i/p < k := (Nat.mul_lt_mul_left hp).mp (by omega)
      refine ⟨i/p, mem_filter.mpr ⟨mem_range.mpr valid, ?_⟩, reconstruct⟩
      simp only [reconstruct, Nat.testBit_mod_two_pow, decide_eq_true bound, Bool.true_and, flag]
  rw [keep, ← remove] at split
  change S.card = _
  omega

def fixedPattern (p width : ℕ) : ℕ := (2^(p*(width/p+2))-1)/(2^p-1)

theorem fixedPattern_spec {p width lo i : ℕ} (hp : 0 < p) (hi : i < width) :
    (fixedPattern p width >>> (lo%p)).testBit i = (packedDivisors p lo width).testBit i := by
  apply Bool.eq_iff_iff.mpr
  rw [packedDivisors_spec hp hi]
  unfold fixedPattern
  rw [Nat.testBit_shiftRight, ← multiplesMask_fast hp, multiplesMask_spec hp]
  have moved : p ∣ lo%p+i ↔ p ∣ lo+i := by
    calc
      p ∣ lo%p+i ↔ p ∣ p*(lo/p)+(lo%p+i) := Nat.dvd_add_iff_right ⟨_,rfl⟩
      _ ↔ p ∣ lo+i := by rw [← Nat.add_assoc, Nat.div_add_mod]
  rw [← moved]
  constructor
  · rintro ⟨j,_,h⟩; exact ⟨j,h⟩
  · rintro ⟨j,h⟩
    have l := Nat.mod_lt lo hp
    have w := Nat.mod_lt width hp
    have q := Nat.div_add_mod width p
    have cover : lo%p+i < p*(width/p+2) := by rw [Nat.mul_add]; omega
    rw [h] at cover
    exact ⟨j,(Nat.mul_lt_mul_left hp).mp cover,h⟩

def clearFixed (mask pattern offset : ℕ) : ℕ := mask ^^^ (mask &&& (pattern >>> offset))

theorem clearFixed_spec {p width lo i mask : ℕ} (hp : 0 < p) (hi : i < width) :
    (clearFixed mask (fixedPattern p width) (lo%p)).testBit i =
      (clearDivisors mask p lo width).testBit i := by
  simp only [clearFixed, clearDivisors, Nat.testBit_xor, Nat.testBit_and, fixedPattern_spec hp hi]
end Astra247824


namespace Astra247824.Leaves
open Finset ArithmeticFunction
def survivors (ps : List ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)

def signedSieve (ps : List ℕ) (x : ℕ) : ℤ := (survivors ps x).card

def descendingPrimes (y : ℕ) : List ℕ :=
  ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse

theorem mem_descending {p y : ℕ} : p ∈ descendingPrimes y ↔ p ∈ Nat.primesLE y := by
  simp [descendingPrimes, Nat.mem_primesLE]

def remainingBound (y d : ℕ) := if d = 1 then y else d.minFac-1

def denominators (y : ℕ) := (Icc 1 y).filter Squarefree

abbrev Edge := Sigma (fun _ : ℕ => ℕ)

def edges (y : ℕ) : Finset Edge :=
  (denominators y).sigma (fun d => Nat.primesLE (remainingBound y d))

def special (y : ℕ) := (edges y).filter (fun e => ¬e.1*e.2 ≤ y)
end Astra247824.Leaves


namespace Astra247824
open Finset Leaves ArithmeticFunction
def segmentCount (ps : List ℕ) (lo width : ℕ) : ℕ :=
  ((range width).filter (fun i => ∀ p ∈ ps, ¬ p ∣ lo+i)).card

theorem segmentCount_add (ps : List ℕ) (lo a b : ℕ) :
    segmentCount ps lo (a+b) = segmentCount ps lo a + segmentCount ps (lo+a) b := by
  let f := fun i => if ∀ p ∈ ps, ¬ p ∣ lo+i then (1:ℕ) else 0
  have eq := sum_range_add f a b
  simpa only [f, Nat.add_assoc, sum_boole, Nat.cast_id, segmentCount] using eq

theorem segmentCount_zero_head (ps : List ℕ) : segmentCount ps 0 1 = if ps = [] then 1 else 0 := by
  cases ps <;> simp [segmentCount]

theorem signedSieve_eq_segment (ps : List ℕ) (t : ℕ) :
    signedSieve ps t = (segmentCount ps 1 t : ℤ) := by
  unfold signedSieve survivors segmentCount
  apply congrArg (fun n : ℕ => (n : ℤ))
  symm
  apply card_bij (fun i _ => 1+i)
  · intro i hi
    obtain ⟨idx,clean⟩ := mem_filter.mp hi
    have h := mem_range.mp idx
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,clean⟩
  · intro i _ j _ h; omega
  · intro n hn
    obtain ⟨idx,clean⟩ := mem_filter.mp hn
    obtain ⟨positive,bound⟩ := mem_Icc.mp idx
    have eq : 1+(n-1) = n := by omega
    refine ⟨n-1,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,eq⟩
    simpa only [eq] using clean

def hardEdges (x y : ℕ) : Finset Edge :=
  (special y).filter (fun e => ¬ x/(e.1*e.2) < e.2^2)
end Astra247824


namespace Astra247824
open Finset Leaves ArithmeticFunction
def tinyPrime (j : ℕ) : ℕ := (#[2,3,5,7,11,13,17,19] : Array ℕ)[j]!

private def tinyCut (j : ℕ) : ℕ := (#[0,2,3,5,7] : Array ℕ)[j]!

private def packedWheel (j : ℕ) : ℕ := (#[0xd2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100,
  0x69696868676766666565646463636262616160605f5f5e5e5d5d5c5c5b5b5a5a59595858575756565555545453535252515150504f4f4e4e4d4d4c4c4b4b4a4a49494848474746464545444443434242414140403f3f3e3e3d3d3c3c3b3b3a3a39393838373736363535343433333232313130302f2f2e2e2d2d2c2c2b2b2a2a29292828272726262525242423232222212120201f1f1e1e1d1d1c1c1b1b1a1a19191818171716161515141413131212111110100f0f0e0e0d0d0c0c0b0b0a0a09090808070706060505040403030202010100,
  0x46464545454544444343434342424141414140403f3f3f3f3e3e3d3d3d3d3c3c3b3b3b3b3a3a3939393938383737373736363535353534343333333332323131313130302f2f2f2f2e2e2d2d2d2d2c2c2b2b2b2b2a2a2929292928282727272726262525252524242323232322222121212120201f1f1f1f1e1e1d1d1d1d1c1c1b1b1b1b1a1a1919191918181717171716161515151514141313131312121111111110100f0f0f0f0e0e0d0d0d0d0c0c0b0b0b0b0a0a0909090908080707070706060505050504040303030302020101010100,
  0x38383737373737373636363635353434343433333232323231313131313130302f2f2f2f2f2f2e2e2e2e2d2d2c2c2c2c2b2b2a2a2a2a29292929292928282727272727272626262625252424242423232222222221212121212120201f1f1f1f1f1f1e1e1e1e1d1d1c1c1c1c1b1b1a1a1a1a19191919191918181717171717171616161615151414141413131212121211111111111110100f0f0f0f0f0f0e0e0e0e0d0d0c0c0c0c0b0b0a0a0a0a09090909090908080707070707070606060605050404040403030202020201010101010100,
  0x30302f2f2f2f2f2f2f2f2f2f2e2e2d2d2d2d2c2c2b2b2b2b2a2a2a2a2a2a2929282828282828272727272626252525252424242424242323232323232222212121212121202020201f1f1e1e1e1e1e1e1d1d1d1d1c1c1c1c1c1c1b1b1b1b1b1b1b1b1a1a1a1a1919181818181717161616161515151515151515141414141414131313131212121212121111101010100f0f0f0f0f0f0e0e0d0d0d0d0d0d0c0c0c0c0c0c0b0b0b0b0a0a0909090908080808080807070606060606060505050504040303030302020101010101010101010100] : Array ℕ)[j]!

private def wheelEntry (j r : ℕ) : ℕ := ((packedWheel j) >>> (8*r)) % 256

private def baseWheel (j x : ℕ) : ℕ := (x/210)*wheelEntry j 210 + wheelEntry j (x%210)

private theorem baseWheel_correct {j : ℕ} (hj : j ≤ 4) (x : ℕ) :
    baseWheel j x = phi tinyPrime j x := by
  have roster : ∀ a : Fin 5, (List.range a.val).map tinyPrime =
      (List.range (tinyCut a.val+1)).filter (fun p => decide p.Prime) := by decide +kernel
  have divides : ∀ a : Fin 5, ∀ p ∈ Nat.primesLE (tinyCut a.val), p ∣ 210 := by decide +kernel
  have tab : ∀ a : Fin 5, ∀ r : Fin 211,
      wheelEntry a.val r.val = phi tinyPrime a.val r.val := by decide +kernel
  let a : Fin 5 := ⟨j, by omega⟩
  have rr (u : ℕ) := rough_eq_phi tinyPrime j (tinyCut j) u (roster a)
  have wheel := rough_wheel (divides a) x
  have one : wheelEntry j 210 = phi tinyPrime j 210 := tab a ⟨210, by decide⟩
  have tail : wheelEntry j (x%210) = phi tinyPrime j (x%210) :=
    tab a ⟨x%210,(Nat.mod_lt _ (by decide : 0<210)).trans_le (by decide)⟩
  change rough (tinyCut j) x = x/210*rough (tinyCut j) 210 + rough (tinyCut j) (x%210) at wheel
  rw [rr x, rr 210, rr (x%210)] at wheel
  unfold baseWheel
  rw [one,tail,wheel]

private def aboveWheel : ℕ → ℕ → ℕ
  | 0 => baseWheel 4
  | r+1 => sieveStep (tinyPrime (4+r)) (aboveWheel r)

private theorem aboveWheel_correct (r : ℕ) : aboveWheel r = phi tinyPrime (4+r) := by
  induction r with
  | zero => funext x; exact baseWheel_correct (by decide) x
  | succ r ih => simp only [aboveWheel, ih, phi]; rfl

def smallRank (j x : ℕ) : ℕ := if j≤4 then baseWheel j x else aboveWheel (j-4) x

theorem smallRank_signed (j : Fin 8) (x : ℕ) :
    (smallRank j.val x : ℤ) = Leaves.signedSieve (Leaves.descendingPrimes (tinyPrime j.val-1)) x := by
  have roster : ∀ a : Fin 8, (List.range a.val).map tinyPrime =
      (List.range ((tinyPrime a.val-1)+1)).filter (fun p => decide p.Prime) := by decide +kernel
  have real : smallRank j.val x = phi tinyPrime j.val x := by
    by_cases h : j.val≤4
    · exact (if_pos h).trans (baseWheel_correct h x)
    · have size : 4+(j.val-4) = j.val := by omega
      simp only [smallRank,if_neg h,aboveWheel_correct,size]
  rw [real, ← rough_eq_phi tinyPrime j.val (tinyPrime j.val-1) x (roster j)]
  simp only [Leaves.signedSieve, Leaves.survivors, Leaves.mem_descending, rough]
end Astra247824


namespace Astra247824
open Finset
def firstIndex (p lo : ℕ) : ℕ := (p-lo%p)%p

private theorem first_aligned {p lo : ℕ} (hp : 0<p) : p ∣ lo+firstIndex p lo := by
  have h := Nat.mod_lt lo hp
  have parts := Nat.div_add_mod lo p
  by_cases z : lo%p=0
  · simp only [firstIndex,z,Nat.sub_zero,Nat.mod_self,Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero z
  · have small : p-lo%p<p := by omega
    simp only [firstIndex,Nat.mod_eq_of_lt small]
    exact ⟨lo/p+1, by rw [Nat.mul_succ]; omega⟩

def stageUpdate (mask rank pattern modulus p lo : ℕ) : ℕ × ℕ :=
  let removed := mask &&& (pattern >>> (lo%p))
  (mask ^^^ removed, rank - ((removed >>> firstIndex p lo) % modulus))

private theorem removed_bits {mask p lo width : ℕ} (hp : 0<p) (bounded : mask<2^width) :
    ((mask &&& (fixedPattern p width >>> (lo%p))) >>> firstIndex p lo) =
      (mask >>> firstIndex p lo) &&& fixedPattern p width := by
  let r := firstIndex p lo
  apply Nat.eq_iff_testBit_eq.mpr
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and]
  change (mask.testBit (r+i) && _) = (mask.testBit (r+i) && _)
  by_cases whereat : r+i < width
  · have iw : i<width := by omega
    have pred (j n : ℕ) (h : j<width) :
        (fixedPattern p width >>> (n%p)).testBit j = true ↔ p ∣ n+j := by
      rw [fixedPattern_spec hp h,packedDivisors_spec hp h]
    have a := pred (r+i) lo whereat
    have b := pred i 0 iw
    simp only [Nat.zero_mod,Nat.shiftRight_zero,Nat.zero_add] at b
    have d : p ∣ lo+(r+i) ↔ p ∣ i := by
      rw [← Nat.add_assoc]
      exact (Nat.dvd_add_iff_right (first_aligned hp)).symm
    have pat : (fixedPattern p width >>> (lo%p)).testBit (r+i) =
        (fixedPattern p width).testBit i := Bool.eq_iff_iff.mpr (a.trans (d.trans b.symm))
    simp only [Nat.testBit_shiftRight] at pat
    exact congrArg (fun flag => mask.testBit (r+i) && flag) pat
  · have none := Nat.testBit_lt_two_pow (i:=r+i)
      (bounded.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [none]

theorem stageUpdate_correct {mask rank p lo width : ℕ} (hp : 0<p) (bounded : mask<2^width)
    (room : width/p+2 < 2^p-1)
    (counted : rank = ((range width).filter (fun i => mask.testBit i)).card) :
    let next := stageUpdate mask rank (fixedPattern p width) (2^p-1) p lo
    (∀ i < width, next.1.testBit i = true ↔ mask.testBit i = true ∧ ¬p ∣ lo+i) ∧
    next.2 = ((range width).filter (fun i => next.1.testBit i)).card := by
  dsimp only [stageUpdate]
  let k := width/p+2
  have cover : width≤p*k := by
    have h := Nat.div_add_mod width p
    have r := Nat.mod_lt width hp
    dsimp only [k]
    rw [Nat.mul_add]
    omega
  let r := firstIndex p lo
  have drop : (((mask &&& (fixedPattern p width >>> (lo%p))) >>> r) % (2^p-1)) =
      denseLane p k r (mask % 2^width) := by
    rw [removed_bits hp bounded, Nat.mod_eq_of_lt bounded]
    rfl
  have eq := ranks_after_clear (mask:=mask) (r:=r) (lo:=lo) (k:=k) hp (Nat.mod_lt _ hp) (first_aligned hp) cover room
  have flags (i : ℕ) (hi : i<width) := clearFixed_spec (mask:=mask) (lo:=lo) hp hi
  have ok : ((range width).filter (fun i => (clearDivisors mask p lo width).testBit i)).card =
      ((range width).filter (fun i => (clearFixed mask (fixedPattern p width) (lo%p)).testBit i)).card := by
    congr 1
    apply filter_congr
    intro i hi
    rw [flags i (mem_range.mp hi)]
  refine ⟨fun i hi => ?_,?_⟩
  · change (clearFixed mask (fixedPattern p width) (lo%p)).testBit i = true ↔ _
    rw [flags i hi,clearDivisors_spec hp hi]
  · change rank - _ = ((range width).filter (fun i => (clearFixed mask (fixedPattern p width) (lo%p)).testBit i)).card
    rw [← ok, counted, drop]
    omega

def stageInvariant (s : ℕ × ℕ) (ps : List ℕ) (lo width : ℕ) : Prop :=
  s.1 < 2^width ∧ (∀ i < width, s.1.testBit i = true ↔ ∀ p ∈ ps, ¬p ∣ lo+i) ∧
    s.2 = segmentCount ps lo width

private theorem cardinal_bits {word lo width : ℕ} {ps : List ℕ}
    (bits : ∀ i < width, word.testBit i = true ↔ ∀ p ∈ ps, ¬p ∣ lo+i) :
    ((range width).filter (fun i => word.testBit i)).card = segmentCount ps lo width := by
  unfold segmentCount
  congr 1
  apply filter_congr
  exact fun i hi => bits i (mem_range.mp hi)

theorem stageInvariant_step {s : ℕ × ℕ} {ps : List ℕ} {p lo width : ℕ}
    (h : stageInvariant s ps lo width) (hp : 0<p) (room : width/p+2 < 2^p-1) :
    stageInvariant (stageUpdate s.1 s.2 (fixedPattern p width) (2^p-1) p lo) (p::ps) lo width := by
  obtain ⟨bound,flags,rank⟩ := h
  let next := stageUpdate s.1 s.2 (fixedPattern p width) (2^p-1) p lo
  have result := stageUpdate_correct (mask:=s.1) (rank:=s.2) (lo:=lo) hp bound room
    (rank.trans (cardinal_bits flags).symm)
  have keep (i : ℕ) (hi : i < width) : next.1.testBit i = true ↔ ∀ q ∈ p::ps, ¬q ∣ lo+i := by
    rw [result.1 _ hi,flags _ hi,List.forall_mem_cons,and_comm]
  exact ⟨Nat.xor_lt_two_pow bound (Nat.and_le_left.trans_lt bound),keep,
    result.2.trans (cardinal_bits keep)⟩

private theorem block_bounded (ps : List ℕ) (lo width : ℕ) :
    blockMask lo width ps < 2^width := by
  induction ps with
  | nil => exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  | cons p ps ih => exact Nat.xor_lt_two_pow ih (Nat.and_le_left.trans_lt ih)

theorem stageInvariant_start {ps : List ℕ} (lo width rank : ℕ) (hp : ∀ p ∈ ps, 0<p)
    (hr : rank = segmentCount ps lo width) :
    stageInvariant (blockMask lo width ps,rank) ps lo width :=
  ⟨block_bounded ps lo width,fun _ hi => blockMask_spec hi hp,hr⟩
end Astra247824


namespace Astra247824.Ordinary
open Finset ArithmeticFunction
private def trialAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => Nat.minFacAux n k
  | fuel+1, k => if n < k*k then n else if k ∣ n then k else trialAux n fuel (k+2)

private theorem trialAux_eq (n fuel k : ℕ) : trialAux n fuel k = Nat.minFacAux n k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [trialAux, Nat.minFacAux]
    split <;> try rfl
    split <;> try rfl
    exact ih _

private def least (n : ℕ) : ℕ := if 2 ∣ n then 2 else trialAux n 105 3

private theorem least_eq (n : ℕ) : least n = n.minFac := by
  simp only [least, trialAux_eq, Nat.minFac]

noncomputable def mu : ℕ → ℕ → ℤ
  | 0, d => moebius d
  | fuel+1, d =>
      if d = 0 then 0 else if d = 1 then 1 else
      let p := least d
      let q := d/p
      if p ∣ q then 0 else -mu fuel q

theorem mu_eq (fuel d : ℕ) : mu fuel d = moebius d := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    by_cases hz : d=0
    · subst d; simp [mu]
    by_cases ho : d=1
    · subst d; simp [mu]
    rw [mu, if_neg hz, if_neg ho, least_eq]
    let p := d.minFac
    let q := d / p
    have hp : p.Prime := Nat.minFac_prime ho
    have prod : q*p = d := Nat.div_mul_cancel (Nat.minFac_dvd d)
    change (if p ∣ q then 0 else -mu fuel q) = moebius d
    split
    next hd =>
      apply Eq.symm
      apply moebius_eq_zero_of_not_squarefree
      intro sf
      apply Nat.squarefree_iff_prime_squarefree.mp sf p hp
      exact prod ▸ Nat.mul_dvd_mul hd (dvd_refl p)
    next hd =>
      rw [ih, ← prod, isMultiplicative_moebius.map_mul_of_coprime
        (hp.coprime_iff_not_dvd.mpr hd).symm, moebius_apply_prime hp, mul_neg_one]
end Astra247824.Ordinary


namespace Astra247824
open Finset Leaves ArithmeticFunction
theorem late_iff {x d p width b : ℕ} (pd : 0<d) (pp : 0<p) (ww : 0<width) :
    b < (x/(d*p))/width ↔ d ≤ x/(p*((b+1)*width)) := by
  change b+1 ≤ (x/(d*p))/width ↔ _
  rw [Nat.le_div_iff_mul_le ww, Nat.le_div_iff_mul_le (Nat.mul_pos pd pp),
    Nat.le_div_iff_mul_le (Nat.mul_pos pp (Nat.mul_pos (by omega) ww))]
  ring_nf

def lateTop (x y p width b : ℕ) : ℕ :=
  min (min y (x/p^3)) (x/(p*((b+1)*width)))
end Astra247824


namespace Astra247824
open Finset Leaves ArithmeticFunction
private theorem cube_limit {x d p : ℕ} (dh : 0<d) (ph : 0<p) :
    p^2 ≤ x/(d*p) ↔ d≤x/p^3 := by
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos dh ph),Nat.le_div_iff_mul_le (pow_pos ph _)]
  ring_nf

theorem hard_denominator_iff {x y d p : ℕ} (pp : p.Prime) :
    (⟨d,p⟩ : Edge) ∈ hardEdges x y ↔
      Squarefree d ∧ p < d.minFac ∧ max p (y/p) < d ∧ d ≤ min y (x/p^3) := by
  constructor
  · intro h
    obtain ⟨hs,hard⟩ := mem_filter.mp h
    obtain ⟨he,cross⟩ := mem_filter.mp hs
    obtain ⟨hd,hp⟩ := mem_sigma.mp he
    obtain ⟨bounds,sf⟩ := mem_filter.mp hd
    obtain ⟨dpos,dy⟩ := mem_Icc.mp bounds
    obtain ⟨avail,_⟩ := Nat.mem_primesLE.mp hp
    change p≤remainingBound y d at avail
    change ¬d*p≤y at cross
    change ¬x/(d*p)<p^2 at hard
    have d1 : d≠1 := by
      rintro rfl
      simp only [remainingBound,if_true,Nat.one_mul] at avail cross
      omega
    simp only [remainingBound,if_neg d1] at avail
    have low : p<d.minFac := by have := pp.two_le; omega
    exact ⟨sf,low,max_lt (low.trans_le (Nat.minFac_le dpos))
      ((Nat.div_lt_iff_lt_mul pp.pos).mpr (not_le.mp cross)), le_min dy ((cube_limit dpos pp.pos).mp (not_lt.mp hard))⟩
  · rintro ⟨sf,least,lower,upper⟩
    obtain ⟨dp,cross⟩ := max_lt_iff.mp lower
    obtain ⟨dy,uc⟩ := le_min_iff.mp upper
    have pd := pp.two_le
    have dpos : 0<d := by omega
    have crosses := (Nat.div_lt_iff_lt_mul pp.pos).mp cross
    have hard := (cube_limit dpos pp.pos).mpr uc
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_sigma.mpr
      ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨dpos,dy⟩,sf⟩,Nat.mem_primesLE.mpr ⟨?_,pp⟩⟩,
      not_le.mpr crosses⟩,not_lt.mpr hard⟩
    simp only [remainingBound, if_neg (by omega : d≠1)]
    omega

def denomWeight (p n : ℕ) : ℤ :=
  ∑ d ∈ (Icc 1 n).filter (fun d => Squarefree d ∧ p<d.minFac), -moebius d

theorem weighted_mixed_rank {x y p width b : ℕ} (pp : p.Prime) (ww : 0<width) :
    ∑ e ∈ (hardEdges x y).filter (fun e => e.2=p ∧ b < (x/(e.1*e.2))/width), -moebius e.1 =
      denomWeight p (lateTop x y p width b) -
      denomWeight p (min (lateTop x y p width b) (max p (y/p))) := by
  let U := lateTop x y p width b
  let L := max p (y/p)
  let D := fun u => (Icc 1 u).filter (fun d => Squarefree d ∧ p<d.minFac)
  let top := D U
  let bot := D (min U L)
  have subset : bot ⊆ top := by
    intro d hd
    obtain ⟨dr,pred⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp dr).1,(mem_Icc.mp dr).2.trans (min_le_left ..)⟩,pred⟩
  let E := (hardEdges x y).filter (fun e => e.2=p ∧ b < (x/(e.1*e.2))/width)
  have loc (d : ℕ) : (⟨d,p⟩ : Edge) ∈ E ↔ d ∈ top \ bot := by
    simp only [E,mem_filter,hard_denominator_iff pp,true_and]
    constructor
    · rintro ⟨⟨sf,lf,lower,upper⟩,late⟩
      obtain ⟨dp,yl⟩ := max_lt_iff.mp lower
      have dpos := pp.pos.trans dp
      have within : d ≤ U := le_min upper ((late_iff (x:=x) dpos pp.pos ww).mp late)
      have hm : d ∈ top := mem_filter.mpr ⟨mem_Icc.mpr ⟨dpos,within⟩,sf,lf⟩
      refine mem_sdiff.mpr ⟨hm,?_⟩
      intro down
      exact (not_le.mpr lower) (((mem_Icc.mp (mem_filter.mp down).1).2).trans (min_le_right ..))
    · intro h
      obtain ⟨up,out⟩ := mem_sdiff.mp h
      obtain ⟨dr,sf,lf⟩ := mem_filter.mp up
      obtain ⟨dpos,within⟩ := mem_Icc.mp dr
      have lower : L<d := by
        by_contra! no
        exact out (mem_filter.mpr ⟨mem_Icc.mpr ⟨dpos,le_min within no⟩,sf,lf⟩)
      obtain ⟨upper,late⟩ := le_min_iff.mp within
      exact ⟨⟨sf,lf,lower,upper⟩,(late_iff (x:=x) dpos pp.pos ww).mpr late⟩
  have indices : E = (top \ bot).image (fun d => (⟨d,p⟩ : Edge)) := by
    ext e
    obtain ⟨d,q⟩ := e
    constructor
    · intro he
      obtain rfl : q=p := (mem_filter.mp he).2.1
      exact mem_image.mpr ⟨d,(loc d).mp he,rfl⟩
    · intro h
      obtain ⟨n,mem,eq⟩ := mem_image.mp h
      exact eq ▸ (loc n).mpr mem
  change (∑ e ∈ E, -moebius e.1) = _
  rw [indices, sum_image (fun a _ b _ h => congrArg Sigma.fst h)]
  change (∑ d ∈ top \ bot, -moebius d) = (∑ d ∈ top, -moebius d) - (∑ d ∈ bot, -moebius d)
  have eq := sum_sdiff subset (f:=fun d => -moebius d)
  omega

theorem hard_prime_upper {y : ℕ} {e : Edge} (he : e ∈ hardEdges 81744924555066 y) : e.2≤3006 := by
  obtain ⟨d,p⟩ := e
  have prime := Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp (mem_filter.mp he).1).1).2
  obtain ⟨_,_,lower,upper⟩ := (hard_denominator_iff prime).mp he
  have dp := (max_lt_iff.mp lower).1
  have fit := (Nat.le_div_iff_mul_le (pow_pos prime.pos 3)).mp (le_min_iff.mp upper).2
  have lt : p^4 < 81744924555066 := by
    calc
      p^4 = p*p^3 := by ring
      _ < d*p^3 := Nat.mul_lt_mul_of_pos_right dp (pow_pos prime.pos 3)
      _ ≤ _ := fit
  change p≤3006
  by_contra! too_large
  have powBound : 3007^4 ≤ p^4 := Nat.pow_le_pow_left (by omega : 3007≤p) 4
  exact (lt_of_le_of_lt powBound lt).not_ge (by decide)
end Astra247824


namespace Astra247824.SquareBand
open Finset Leaves ArithmeticFunction
abbrev X : ℕ := 81744924555066

abbrev Y : ℕ := 43399

abbrev W : ℕ := 65536

abbrev S : Finset Edge := (hardEdges X Y).filter (fun e => 23<e.2)

def stages := S.image (fun e => e.2)

def weight (p b : ℕ) : ℤ :=
  ∑ e ∈ S.filter (fun e => e.2=p ∧ b < (X/(e.1*e.2))/W), -moebius e.1

def cell (p b : ℕ) : ℤ := (segmentCount (descendingPrimes (p-1)) (b*W) W : ℤ)*weight p b

private theorem p_prime {e : Edge} (he : e ∈ hardEdges X Y) : e.2.Prime :=
  Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp (mem_filter.mp he).1).1).2

theorem stage_subset : stages ⊆ Nat.primesLE 3006 := by
  intro p hp
  obtain ⟨e,h,rfl⟩ := mem_image.mp hp
  have member := (mem_filter.mp h).1
  exact Nat.mem_primesLE.mpr ⟨hard_prime_upper member,p_prime member⟩

theorem absent {p : ℕ} (h : p ∉ stages) (b : ℕ) : weight p b = 0 := by
  unfold weight
  apply sum_eq_zero
  intro e he
  obtain ⟨whereat,atp,_⟩ := mem_filter.mp he
  exact (h (mem_image.mpr ⟨e,whereat,atp⟩)).elim

private def allCells : ℤ := ∑ b ∈ range 28740, ∑ p ∈ stages, cell p b

private theorem original_count {p : ℕ} (lo length : ℕ) (h : 23<p) :
    ((range length).filter (fun i => 0<lo+i ∧
      (descendingPrimes (p-1)).all (fun q => decide (¬q ∣ lo+i)))).card =
        segmentCount (descendingPrimes (p-1)) lo length := by
  have two : 2 ∈ descendingPrimes (p-1) := mem_descending.mpr (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩)
  unfold segmentCount
  congr 1
  ext i
  simp only [mem_filter,List.all_eq_true,decide_eq_true_eq]
  constructor
  · exact fun ⟨hi,_,clean⟩ => ⟨hi,clean⟩
  · rintro ⟨hi,clean⟩
    refine ⟨hi,?_,clean⟩
    by_contra! outside
    have zero : lo+i=0 := by omega
    exact (clean 2 two) (by rw [zero]; exact dvd_zero 2)

private theorem exact_target :
    OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H3 ↔ allCells = 3360343589286 := by
  let R := ((special Y).filter (fun e => e.2^2≤X/(e.1*e.2))).filter (fun e => 23<e.2)
  let old (p b : ℕ) := ((range W).filter (fun i => 0<b*W+i ∧
      (descendingPrimes (p-1)).all (fun q => decide (¬q ∣ b*W+i)))).card
  have idx : R=S := by
    ext e
    simp only [R,S,hardEdges,mem_filter,not_lt]
  change (∑ b ∈ range 28740, ∑ p ∈ R.image (fun e => e.2), (old p b : ℤ) *
    (∑ e ∈ R.filter (fun e => e.2=p ∧ b<(X/(e.1*e.2))/W), -moebius e.1)) = _ ↔ _
  rw [idx]
  have equal : (∑ b ∈ range 28740, ∑ p ∈ S.image (fun e => e.2), (old p b : ℤ)*weight p b) = allCells := by
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro p hp
    obtain ⟨e,he,rfl⟩ := mem_image.mp hp
    have gt := (mem_filter.mp he).2
    exact congrArg (fun v : ℕ => (v : ℤ)*weight e.2 b) (original_count _ _ gt)
  change (∑ b ∈ range 28740, ∑ p ∈ S.image (fun e => e.2), (old p b : ℤ)*weight p b) = _ ↔ _
  rw [equal]

theorem h3_iff_cells :
    OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H3 ↔
      (∑ b ∈ range 28740, ∑ p ∈ stages, cell p b) = 3360343589286 := exact_target
end Astra247824.SquareBand


namespace Astra247824.GlobalRank
open Finset

/- The population counts of all 256 possible bytes, packed in nibbles. -/
private def bytePopTable : ℕ := 0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110
private def bytePop (w : ℕ) : ℕ := (bytePopTable >>> (4*(w%256))) % 16

private def bitSum (w n : ℕ) : ℕ := ∑ i ∈ range n, if w.testBit i then 1 else 0

private theorem byte_eval : ∀ v : Fin 256, bytePop v.val = bitSum v.val 8 := by
  decide +kernel

private theorem byte_spec (w : ℕ) : bytePop w = bitSum w 8 := by
  have h := byte_eval ⟨w%256, Nat.mod_lt _ (by decide)⟩
  change bytePop (w%256) = bitSum (w%256) 8 at h
  rw [show bytePop (w%256) = bytePop w by simp [bytePop]] at h
  rw [h]
  unfold bitSum
  apply Finset.sum_congr rfl
  intro i hi
  have hi8 := Finset.mem_range.mp hi
  change (if (w%2^8).testBit i then _ else _) = _
  rw [Nat.testBit_mod_two_pow w 8 i]
  simp only [decide_eq_true hi8, Bool.true_and]

private def popBytes (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => popBytes w n + bytePop (w >>> (8*n))

private theorem popBytes_spec (w n : ℕ) : popBytes w n = bitSum w (8*n) := by
  induction n with
  | zero => simp [popBytes, bitSum]
  | succ n ih =>
    rw [popBytes, ih, byte_spec]
    unfold bitSum
    rw [Nat.mul_succ, Finset.sum_range_add]
    simp [Nat.testBit_shiftRight]

/- Number of set bits of a 64-bit word. -/
def pop64 (w : ℕ) : ℕ := popBytes w 8

theorem pop64_spec (w : ℕ) (_hw : w < 2^64) :
    pop64 w = ((Finset.range 64).filter fun i => w.testBit i = true).card := by
  rw [pop64, popBytes_spec]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

end Astra247824.GlobalRank

namespace Astra247824.HardTail.Scan
def roster : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem roster_eq : roster = (List.range 3007).filter (fun p => decide p.Prime) := by
  trans (List.range 3007).filter (fun p => decide (2 ≤ p ∧ p.minFac = p))
  · decide +kernel
  · apply List.filter_congr
    intro p _
    exact decide_eq_decide.mpr Nat.prime_def_minFac.symm
theorem roster_mem (p : ℕ) : p∈roster ↔ p ≤ 3006 ∧ p.Prime := by
  simp [roster_eq,Nat.lt_succ_iff]
theorem roster_sorted : roster.Pairwise (·<·) := by rw [roster_eq]; exact List.pairwise_lt_range.filter _


end Astra247824.HardTail.Scan

namespace Astra247824.CompactWeights
def seed : ℕ := 0x800020a20208000800000000200820008028800200020000200000000200008000000000208020000000000808000020000008008000008000000800800200220a00008000008020800800020000200000820000000000000028020000000a00020808208800008000800020200000000008000000000008020000200000200000200000000800000000020a00000820200000000008000208000a00000820000800000000008000020000008020020000000000000000020000008000020200000008800008000000820000228000000008800220820008000000000800000000020008800800220800000200000028000020000000200800000000200800808020020a08208000200000000000008008000000000008000020000000008008000800020000220000008008028028000800000020200000a00200000000020000008000000000200220020008a00000000000220220008028008000000200000820200200000200020000000008000020000200000820008208800200028020020a20800800808008000000a08808000000000000020200200000208020008020000000020000800000020028008800800228000020000000000000200000808000000200020800208000208000000020000028000000200000008000000020800000020000220000008000200220820008000000800000000020a00000000020800a00200000000800808000800208000000008000000200000028008000020200000028020000008200000000000800200820020000200200800208000200008020000000000800000000a00000800000000000000000828000000000208800020820800220000000800200a28800000800000800800000000000020008000820008000020000000800820020008200008200808020200000000020200a00200000008020000200208000220200008000000000220008800020000020a00800000208200808000008220000000200800000800000200000000000008000000000200200800000000000008828000000000808020808000000800000800000200a00008000008000000228000228000200000000208000000000800000200a08200000000020000000000220000008028000000000800200000020800000020008000000000800820020000008008000000220000200008000200008000000000000000200808000a00800008808020000800000020008000000800800000000008800020208000208800020000800200a00008200000800800000000000000220828008000200000020000000008000020208000000820800000a00008020000028200200220808000200800800008000200800000000000200000008008000000200200000020800200000020200000008200000000a00200a00008020020008800000000820000000000000000000000828200000800a00800208000008020820008000200020020000000808220000008020000000000200020a00008020020000000020820020000000a08000208000000000000000000000028000008020000820808200000008000000000000800208000000200000000800220000208000000000220008028828000000208200000028800200220000008000000800808000800000020020000a00000820000000000008008000008220200020828200000000000000000000800800000000000000808000000800008028000000200200000820000000008000000000820000808008208220000200000020020000800800020200000000800000800000200020000000000028800000000000a08020200800200000008008000000200000000800808000020020020808008008020000000200020000000800000008000000200200000028020000000008008000000000008000000800020800208000000808000020000000008000000000000008820200000000000800200820000000008000200a00208028000820000a00020200000800800000020a20000020800000000200020008000000800008020220000200008020200000200800000000000008a20008020020808000000200800800000000220200200800020000800000000020000000200000000200000800800000008200208200020008020000020808000000200200800008800000200800000000000008000000000208828020000000808020000000000208800828008200000008000000800000000800200a00800800000020020000200020200000000000028008200008200000008200000020008008020008000800000200008000800220000800000808208020000008020200000000028000000020000800000008020000800000028020000820800000220000208008000000000028000000000008800020000800200800808000200000020000000000200220000020200000800000200000000000008200000000208000020800000808000200800200000828000000800a28020028000008800000008000800200000000200200008028000800000200020200000000000000208000000000000000200008000000000000a00000000028000800820000000a20000200020000a00000208020000000000000020008a00000020808008000000220020000220008000008200000000000000220800000208008000000000020000008020800200000000200000000800000020000000008008000000800820020200000820000220000808020000000000000a08000200000800000000200800208028008000800808208000000000008200000220200000820800020200000020028000200200000000000000208800800020020208000000000000200800000028020000200800000020800820000200800000000000000000800800000020820008800000008800200008800000000808008020008a00000020000000000008800000020000800008820020000000020008008000000800800020020008000020200020208208000000800200000008000020000200000000200000208000200800000028800008020200200000000000200800020000200800200000000000800020808008000000028008020220000008000028000000220808000000800008000000020008028000000200000200008008000000800020200000000000008000800208000028020000800000020020000a00000020008a00000000008000800800200008000000808000820008000000000000200220000220020020200200820008000800808000800008220000020000000020008000000008200000820800028000000220000000220200000000000a00000808008000000000000800208000000000008000000008008028008800000000000000200008800000000020800000000000000200208820000000000a08020000000000008800000000000020020000200200800800220000008008800200a20008000800020800000000020008800200000000200000008000000008200200800000000820000000000200000000808800020000a00000800020800200820000020820200000000000000000020000200800008000020000820000000000000220000a00000000020008020808228000000800000008000808000800000220000808800200000200000020000020008020808000220008000000000000000000020000000000000008008000000808000020200000000008008820000000000020800200200000000200000028008000000800200800200000a00000000000800000000000200000200000008200020208000020020000200000020220000800008000220000800028008000000200000020208000000000800200800000800000200220000000000028000800000020000000000000000020800000228828000800000200000000020000008020008000000808000200820200208000028020000000000200020800020808200020200020000000200000008000000000008808000000020008800820000800800000000000000800000008208200000200000000020008000000008000800820000020020008808000008020208000000008a00200000000020000000020000208000800a08000000000000000020020000200808000200000000008000000000000000000008000800a00000008800800200000000200008000008020020000020800008000200820000000000208800800008800008008020000000008000020000220800200820208020000000008000200000200820020800000020008000800800808000000000200800000208000a00200000008800000200008028000808000000020000008000000000a00000000800000000208200000008820000000000200800800800000000000008a00028000000000000800200000000000800220200000000028200000000000800200200008008020000000800020008000220000020800000020008028000200000000020000208200000000008000000008000000000000000000808008a00208000008000200000a00000000200800028000000000808200000000000200800000020020000000000020020000020800000020000200028020200a00000000008020000200000020000000200000200000a00808000000800800200000000800208800020000000208008000000000808000000020020000a08008000a00000020008000000800208800000020200000000000000008800028200000200000000028800800000000000000800220008200000800000028000000000000020008800000200000000000000008000200020008220008020020008000020020000000200000000820000000000008800000008000200000000008800020200200000008000800800020000000020200000000028000008000808000200000000020200200000820000200820200200000020800000000000000000000808020020200000800800000020000000008000000000000800008000800220000200000200000000200200008828000000020200808008000020000020808200000000008800000220200008020020000000000008000820000000800220000008800008000000000000020008820000200020000000800000800200000008000000008000000008020020800200808020000000200008000200800000800008000800000020000200200000020000000a00208000020000000800020828200000000200000000000000000020008200800008008000020200000000000000800020000000020800008008208000000200000200000800200000028000000800800000800200000008008000000000000200000000000000020000200008000000800000008820020000000a00800000800000000800000000000028000020000000a00800000000808800008000000800220000200000000000000020000800800000200020000000008000020000028000020200200000000000000008828008000800008008020208800000200020008000000000020000000000020000008020800a00000008000208000000020000000020800000000208000000008000200008000000000000008020020a00200000020000200808000028000000000220000000200008800800200800008200000000200000000008020000000000000000000000820020208220000800000000200800000820000000008200008000800200000000000000800200020020000200000800008000000000800000820000000000000020000020808000200808000000200800000200000000200200020800008000000a00000000200000008800000a00000000000000200000200000220020008020000000820200000800000000000000000000000200800000200000000020820008000808800000000000800000008028000008000000000000208028000008000000200000020020000000000008020200000020000000808000000000000800220000000000000008000000000000008008200200800000800000020200000000028000000828000200000000020028000800000200008000200000800000000000a00000000200200000000008200020800000000000820000008000000800008008008008020000000000200020000000000020000800008800000a00000000808020000000200000000a00000000000000020000008000000000000800000200000800000008000200200000808208800000800000200800200000020000000008000000000200a00000020000000000a20020008000000208000020800000000000000800000020020208000000000800000000000000000008000800008000000020008000800020000008000000000000000200020208000000a20000000000000a08000008200000000000000000000820000000800000000000000000000008008020220000000000028000000200008000000800000000020820208800000000220000028000000000000000000020000000200800000000008000008000000800000000200020a00000800000200200000000200000000000028000000200000000000000808020000000000800020000000000800000000008000008200000000a00008000000000000208020000020000000000000000000000000000000020800000808008200000800000000000000200800000020000800820000200000020008000200000000008000000000000000000000200020000020000000800800000000008008000028000000000000008000008000000028a0080000002000000000000080000020000002000000000000020000820002000000002000000020000000000800080000000000080000020000020000000000000002000000000000802000020000800000000000800000000000000000800000082000080000000002000020000020000000000000820000000002000000000020080880000000000000800020000000000080020000000000000000080080000002000800000000000000000000002000800800000000002000000000000000000880000000000020000000020000000020080080000002000000080000000000000000000000000000000000800082000000000000020000802000000000000000000000002000000000000020000000000000020000000080000000080000000000000020000000000000000800000800000000000000000000000800000000000080000000000000000020000000000000020000000000000000000000000000002000000000000000800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def cleared (w p : ℕ) := w ^^^ (w &&& (((1 <<< (p*(43400/p+1)))-1)/((1 <<< p)-1)))
private def neg29 : {w : ℕ // seed=w} := ⟨_,by conv => lhs; whnf⟩
private def neg31 : {w : ℕ // cleared neg29.1 31=w} := ⟨_,by conv => lhs; whnf⟩
private def neg37 : {w : ℕ // cleared neg31.1 37=w} := ⟨_,by conv => lhs; whnf⟩
private def neg41 : {w : ℕ // cleared neg37.1 41=w} := ⟨_,by conv => lhs; whnf⟩
private def neg43 : {w : ℕ // cleared neg41.1 43=w} := ⟨_,by conv => lhs; whnf⟩
private def neg47 : {w : ℕ // cleared neg43.1 47=w} := ⟨_,by conv => lhs; whnf⟩
private def neg53 : {w : ℕ // cleared neg47.1 53=w} := ⟨_,by conv => lhs; whnf⟩
private def neg59 : {w : ℕ // cleared neg53.1 59=w} := ⟨_,by conv => lhs; whnf⟩
private def neg61 : {w : ℕ // cleared neg59.1 61=w} := ⟨_,by conv => lhs; whnf⟩
private def neg67 : {w : ℕ // cleared neg61.1 67=w} := ⟨_,by conv => lhs; whnf⟩
private def neg71 : {w : ℕ // cleared neg67.1 71=w} := ⟨_,by conv => lhs; whnf⟩
private def neg73 : {w : ℕ // cleared neg71.1 73=w} := ⟨_,by conv => lhs; whnf⟩
private def neg79 : {w : ℕ // cleared neg73.1 79=w} := ⟨_,by conv => lhs; whnf⟩
private def neg83 : {w : ℕ // cleared neg79.1 83=w} := ⟨_,by conv => lhs; whnf⟩
private def neg89 : {w : ℕ // cleared neg83.1 89=w} := ⟨_,by conv => lhs; whnf⟩
private def neg97 : {w : ℕ // cleared neg89.1 97=w} := ⟨_,by conv => lhs; whnf⟩
private def neg101 : {w : ℕ // cleared neg97.1 101=w} := ⟨_,by conv => lhs; whnf⟩
private def neg103 : {w : ℕ // cleared neg101.1 103=w} := ⟨_,by conv => lhs; whnf⟩
private def neg107 : {w : ℕ // cleared neg103.1 107=w} := ⟨_,by conv => lhs; whnf⟩
private def neg109 : {w : ℕ // cleared neg107.1 109=w} := ⟨_,by conv => lhs; whnf⟩
private def neg113 : {w : ℕ // cleared neg109.1 113=w} := ⟨_,by conv => lhs; whnf⟩
private def neg127 : {w : ℕ // cleared neg113.1 127=w} := ⟨_,by conv => lhs; whnf⟩
private def neg131 : {w : ℕ // cleared neg127.1 131=w} := ⟨_,by conv => lhs; whnf⟩
private def neg137 : {w : ℕ // cleared neg131.1 137=w} := ⟨_,by conv => lhs; whnf⟩
private def neg139 : {w : ℕ // cleared neg137.1 139=w} := ⟨_,by conv => lhs; whnf⟩
private def neg149 : {w : ℕ // cleared neg139.1 149=w} := ⟨_,by conv => lhs; whnf⟩
private def neg151 : {w : ℕ // cleared neg149.1 151=w} := ⟨_,by conv => lhs; whnf⟩
private def neg157 : {w : ℕ // cleared neg151.1 157=w} := ⟨_,by conv => lhs; whnf⟩
private def neg163 : {w : ℕ // cleared neg157.1 163=w} := ⟨_,by conv => lhs; whnf⟩
private def neg167 : {w : ℕ // cleared neg163.1 167=w} := ⟨_,by conv => lhs; whnf⟩
private def neg173 : {w : ℕ // cleared neg167.1 173=w} := ⟨_,by conv => lhs; whnf⟩
private def neg179 : {w : ℕ // cleared neg173.1 179=w} := ⟨_,by conv => lhs; whnf⟩
private def neg181 : {w : ℕ // cleared neg179.1 181=w} := ⟨_,by conv => lhs; whnf⟩
private def neg191 : {w : ℕ // cleared neg181.1 191=w} := ⟨_,by conv => lhs; whnf⟩
private def neg193 : {w : ℕ // cleared neg191.1 193=w} := ⟨_,by conv => lhs; whnf⟩
private def neg197 : {w : ℕ // cleared neg193.1 197=w} := ⟨_,by conv => lhs; whnf⟩
private def neg199 : {w : ℕ // cleared neg197.1 199=w} := ⟨_,by conv => lhs; whnf⟩

def negative : ℕ → ℕ
  | 29 => neg29.1
  | 31 => neg31.1
  | 37 => neg37.1
  | 41 => neg41.1
  | 43 => neg43.1
  | 47 => neg47.1
  | 53 => neg53.1
  | 59 => neg59.1
  | 61 => neg61.1
  | 67 => neg67.1
  | 71 => neg71.1
  | 73 => neg73.1
  | 79 => neg79.1
  | 83 => neg83.1
  | 89 => neg89.1
  | 97 => neg97.1
  | 101 => neg101.1
  | 103 => neg103.1
  | 107 => neg107.1
  | 109 => neg109.1
  | 113 => neg113.1
  | 127 => neg127.1
  | 131 => neg131.1
  | 137 => neg137.1
  | 139 => neg139.1
  | 149 => neg149.1
  | 151 => neg151.1
  | 157 => neg157.1
  | 163 => neg163.1
  | 167 => neg167.1
  | 173 => neg173.1
  | 179 => neg179.1
  | 181 => neg181.1
  | 191 => neg191.1
  | 193 => neg193.1
  | 197 => neg197.1
  | 199 => neg199.1
  | _ => 0


private def column1 : {w : ℕ // (neg29.1 ^^^ neg31.1) ||| (neg41.1 ^^^ neg43.1) ||| (neg43.1 ^^^ neg47.1) ||| (neg53.1 ^^^ neg59.1) ||| (neg61.1 ^^^ neg67.1) ||| (neg67.1 ^^^ neg71.1) ||| (neg73.1 ^^^ neg79.1) ||| (neg79.1 ^^^ neg83.1) ||| (neg101.1 ^^^ neg103.1) ||| (neg103.1 ^^^ neg107.1) ||| (neg113.1 ^^^ neg127.1) ||| (neg127.1 ^^^ neg131.1) ||| (neg137.1 ^^^ neg139.1) ||| (neg149.1 ^^^ neg151.1) ||| (neg157.1 ^^^ neg163.1) ||| (neg163.1 ^^^ neg167.1) ||| (neg173.1 ^^^ neg179.1) ||| (neg181.1 ^^^ neg191.1) ||| (neg197.1 ^^^ neg199.1) = w} := ⟨_, by conv => lhs; whnf⟩
private def column2 : {w : ℕ // (neg29.1 ^^^ neg31.1) ||| (neg31.1 ^^^ neg37.1) ||| (neg43.1 ^^^ neg47.1) ||| (neg47.1 ^^^ neg53.1) ||| (neg59.1 ^^^ neg61.1) ||| (neg67.1 ^^^ neg71.1) ||| (neg73.1 ^^^ neg79.1) ||| (neg97.1 ^^^ neg101.1) ||| (neg101.1 ^^^ neg103.1) ||| (neg107.1 ^^^ neg109.1) ||| (neg113.1 ^^^ neg127.1) ||| (neg139.1 ^^^ neg149.1) ||| (neg149.1 ^^^ neg151.1) ||| (neg151.1 ^^^ neg157.1) ||| (neg163.1 ^^^ neg167.1) ||| (neg167.1 ^^^ neg173.1) ||| (neg179.1 ^^^ neg181.1) ||| (neg181.1 ^^^ neg191.1) ||| (neg193.1 ^^^ neg197.1) ||| (neg197.1 ^^^ neg199.1) = w} := ⟨_, by conv => lhs; whnf⟩
private def column3 : {w : ℕ // (neg29.1 ^^^ neg31.1) ||| (neg37.1 ^^^ neg41.1) ||| (neg41.1 ^^^ neg43.1) ||| (neg43.1 ^^^ neg47.1) ||| (neg53.1 ^^^ neg59.1) ||| (neg59.1 ^^^ neg61.1) ||| (neg71.1 ^^^ neg73.1) ||| (neg73.1 ^^^ neg79.1) ||| (neg83.1 ^^^ neg89.1) ||| (neg103.1 ^^^ neg107.1) ||| (neg107.1 ^^^ neg109.1) ||| (neg113.1 ^^^ neg127.1) ||| (neg131.1 ^^^ neg137.1) ||| (neg137.1 ^^^ neg139.1) ||| (neg151.1 ^^^ neg157.1) ||| (neg167.1 ^^^ neg173.1) ||| (neg181.1 ^^^ neg191.1) = w} := ⟨_, by conv => lhs; whnf⟩
private def column4 : {w : ℕ // (neg29.1 ^^^ neg31.1) ||| (neg47.1 ^^^ neg53.1) ||| (neg53.1 ^^^ neg59.1) ||| (neg59.1 ^^^ neg61.1) ||| (neg79.1 ^^^ neg83.1) ||| (neg83.1 ^^^ neg89.1) ||| (neg109.1 ^^^ neg113.1) ||| (neg113.1 ^^^ neg127.1) ||| (neg139.1 ^^^ neg149.1) ||| (neg149.1 ^^^ neg151.1) ||| (neg151.1 ^^^ neg157.1) ||| (neg173.1 ^^^ neg179.1) ||| (neg179.1 ^^^ neg181.1) ||| (neg181.1 ^^^ neg191.1) = w} := ⟨_, by conv => lhs; whnf⟩
private def column5 : {w : ℕ // (neg31.1 ^^^ neg37.1) ||| (neg37.1 ^^^ neg41.1) ||| (neg41.1 ^^^ neg43.1) ||| (neg43.1 ^^^ neg47.1) ||| (neg47.1 ^^^ neg53.1) ||| (neg53.1 ^^^ neg59.1) ||| (neg59.1 ^^^ neg61.1) ||| (neg89.1 ^^^ neg97.1) ||| (neg97.1 ^^^ neg101.1) ||| (neg101.1 ^^^ neg103.1) ||| (neg103.1 ^^^ neg107.1) ||| (neg107.1 ^^^ neg109.1) ||| (neg109.1 ^^^ neg113.1) ||| (neg113.1 ^^^ neg127.1) ||| (neg157.1 ^^^ neg163.1) ||| (neg163.1 ^^^ neg167.1) ||| (neg167.1 ^^^ neg173.1) ||| (neg173.1 ^^^ neg179.1) ||| (neg179.1 ^^^ neg181.1) ||| (neg181.1 ^^^ neg191.1) = w} := ⟨_, by conv => lhs; whnf⟩
private def column6 : {w : ℕ // (neg61.1 ^^^ neg67.1) ||| (neg67.1 ^^^ neg71.1) ||| (neg71.1 ^^^ neg73.1) ||| (neg73.1 ^^^ neg79.1) ||| (neg79.1 ^^^ neg83.1) ||| (neg83.1 ^^^ neg89.1) ||| (neg89.1 ^^^ neg97.1) ||| (neg97.1 ^^^ neg101.1) ||| (neg101.1 ^^^ neg103.1) ||| (neg103.1 ^^^ neg107.1) ||| (neg107.1 ^^^ neg109.1) ||| (neg109.1 ^^^ neg113.1) ||| (neg113.1 ^^^ neg127.1) ||| (neg191.1 ^^^ neg193.1) ||| (neg193.1 ^^^ neg197.1) ||| (neg197.1 ^^^ neg199.1) = w} := ⟨_, by conv => lhs; whnf⟩
private def column7 : {w : ℕ // (neg127.1 ^^^ neg131.1) ||| (neg131.1 ^^^ neg137.1) ||| (neg137.1 ^^^ neg139.1) ||| (neg139.1 ^^^ neg149.1) ||| (neg149.1 ^^^ neg151.1) ||| (neg151.1 ^^^ neg157.1) ||| (neg157.1 ^^^ neg163.1) ||| (neg163.1 ^^^ neg167.1) ||| (neg167.1 ^^^ neg173.1) ||| (neg173.1 ^^^ neg179.1) ||| (neg179.1 ^^^ neg181.1) ||| (neg181.1 ^^^ neg191.1) ||| (neg191.1 ^^^ neg193.1) ||| (neg193.1 ^^^ neg197.1) ||| (neg197.1 ^^^ neg199.1) = w} := ⟨_, by conv => lhs; whnf⟩
def plane : ℕ → ℕ
  | 0 => seed
  | 1 => column1.1
  | 2 => column2.1
  | 3 => column3.1
  | 4 => column4.1
  | 5 => column5.1
  | 6 => column6.1
  | 7 => column7.1
  | _ => 0

def unpackRanks (lane width : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, value, data =>
    value ||| (unpackRanks lane width n (value + data % (1 <<< width)) (data >>> width) <<< lane)

end Astra247824.CompactWeights

namespace Astra247824.HardTail
open ArithmeticFunction

/- The bits of a denominator index select its prime status and, for eligible
squarefree semiprimes, the eight bits of its smaller prime factor. The kernel
checks these tables against the Möbius function and minimum prime factor. -/

private def primeWord : ℕ := 0xa08000000000000008028200000808008020000020008000820020020000808000200020008020000008800a00200008200800200800820200820208000028000000008820028020200000220800208000808200808020a20208200800020a00000008000020020a00200000200000200808800208a20808220000028820800820008020020808000808200a00000200008008a00200220828020020000808000000200208028020000800008a20008000a00200a20820008000808220808000800a08000000220200000208028000020200800000008200200808820008220a08220008000000208800028208000800800800200800000028008028200000208020200000000800020020820008028820200a00208a00020020a00800220000000220000208808000820800020000200200200820800000820008800800228200208820020008000808808008000000200a20000000000000a00800020020808200008000800a00800808208800800800000228800000000800000220808000000000000208200000200220800020000220020208028000028800800820800000800000a08000220000208808000200020200000020008820208200828028200000808008020200200020808020800000808808000000808800800000200208008020000200a08800000000200808800008020020008028808000a00008220020200000000008028228020200808020000a20000820008208820200800000008a00008800000200020800820000200a20008008000208200800820020000800808000800028020208028808200020a00028008020000a08020000028220008000000000200000000028228000800000000200020800008000228220008800820200200000a08008000220208200800220000000820000000800200020808000000800228800008820800000000008020200808020208000800028008000a00000000800000020000828000000820208020008008000a00828820028020200208820220800008000820000800200200008020a20000a00020228000000220000200800008200028020200800800008000820000200800000220200800028200820000820000008800a08820028008020800200800200200200028828008200200800020220020808208000200820200000808008800808808020028800000220008228020800020000000000208020000200a00000820808200020208008020020020200008800000200800208000028020008020820000020000228808200820208008000200800800a00008020800800a08000020a20000008008208000a00000000000020800000000000020008228000220000008228820028000800000020028020008800820200200008020008008820800008028008020800000820000200000008008220200200208808020a00200828000008800000000020000a00200800008200020008208000028a00000800800000200008a00808020200008020808208000a00008000208800a08000000020820000828028008800a00200008020200008000020028200800200808200a20008020828200000800228000000800800a00820028800000000000000220000828008000020000000820000220808008000220000808208000028000a00208000228020a00800020200800000800000008220208a20028028220208000800220200008020808020220000000800220800800200008228800a00208020028000000000800000800808808028000200a00000008208000808028000220020208020008208800a00200028200020a00000800020000008828000000a20208808000020000000a20800208000000020800200200a08000808220a00000228000008820800800800000a00208028020000220a08820020008a00208a00000000220800220000200800a08020008000a00000a00008020820208a08000028000208008020200820000000000008000808020008028000000200008200000a00008020028a00000800800008820208000800008200008020800008a00800228000020220200000000000000000228808000020000220828008000000208808228020808800000220a20000828808000a00000008028020800800820008200000008208000020220800008000200200a00828028020020208000020200820000000800208820200208020020820800000000200020000a20008020020200228000028000200008800000800a00000800008200008820800200000a00820020000800808200820020200000a20008220820a00008008008000200028000020800000800800008220000000028208800800220008000800200000028200200008200000000800a08000020220000800800820228000000208800000200008020000200820208008028028800008000808208000808200800020000808008020028200800820800208020a08000020000020008800000208a20200000008000200200020820020200000808808000820000220800220000800828000020800808200800020a20208008828008820800828008028220000220008200020008000808220000a08020800000000a00000008028020208a00000000000200808020000a00008008000000800a00a00820020020800008808000220008000820208a00000a00020200800000008800008820208828008208800a08a20000000220a00020000208000800208000000a00000008028028000200000828000020200208800028020000000820000020200000008000a20800820028000000800208008000000008000800028800800220828000800800208000208200000828800008200008028028000a00200820020200200008200008000020a08228028208a00200000820208000000208000200220000800000200220200800008020020808200808208000800200808000220200220000008a00a00200800020800208208020200200000828808000800000020020020220008a00020020000808828008200800200020800028200000800028200000808800820200020008020008208020008820020020a00208a00020000220008000000000000a08220808000800a00008000208020208800020028a00000000020208820200800000020800a08020800008220800200800200020000228000200000200a08800200800008a00800020020000808820000200200820020008800200020000020020808208008000000808008000200000800008800208020200800020220000008800028208000800828008000020200200000000200000008808020800008200028020000800220020228820808208020020800208800820200220800200000020020a00820808220020000028808200200200020820208a00000800000028020a08000000228800208820020008a20200a08000020020000020008008000800200008000000a00200008208200800228008020000800000800020a20200020808000800800200008008200808a20028028220808020000200a00008200020008200000208028200000000208800008820200008028008220200a08008020000808a00028200000000028800020a00800008020000a00200020820200000200208020028000208000000008800808a28008008000200000000220000800a20800220800a00028008208800800a08800200820800200020000820200008000200200808808028000220008800800208020800a00800200200008020020028000000228028028020208a00000020a20008828820008000000020008008220808a00000008200008a20000000820200000800008200800028808020820208800020008200200000828000000808a28020000a00008800808020200008a00808200020200000000028000200028008228800800a00800200200008000028008000800820000000800a08020020028000008a00000000a00800008808220000200a20820208800000200800020200200028008000200008220020028800208220820020000808008800020a00800228008200a00200200808200000a00000820200a00000820020200020008828008008020200a00820000200000000000020820008208008200a00800000820020820a08200820228a20008008828200000000020008020200200020808020020800828800000a00008200028000200000000828220000800208000220200000820008008000000a28008000000200800008000000008220800200020208008008200200800808020000020000200000208800000020028000a20008020020000220808820800200220000808800200200200028820028000200228000220820800808020020000208028828000020200200028028a00000020000028220800a00008020a00a08008020000800800a00800008000a08000020028020200020800000a00200a00000008800200a00028220000800800008020020a08208800020800800a00020228820000808020208220000828000000020000808000028800a08000808000020008200808200020000020820228200800020828000800008208820000a00208808000000800a08008000008000008800820020000008828000200220a00028008008800000020820208000200800000208220000028800208220800000020020a00200820008000200000020800220000a08200000228800000000028008000808208800228a20000020000008200800028008000020008820820028220000800000000820208208800208200200a28800000000008808820028a00200800820000a00200808020008000800220000208200808800800200200808220028020000a00820808028020a08800020208020000820800200200200a08020008200808220020200000800220000000800200208808020800000208808028000808008820200020008808808208220808220008000800200220008228200000028000000a20a08220008000800200800020028020808808820028000200000820008a00008020020000000a08000020008020000220008220800000000800008a00800208000220000a00a00000008800000028020208a00008a20008000200a00000808020200008a08000020a00a00228828020000200020808200020800200800200020008020008008020208208020000220800a00020008000000a08800220020800000808020200200a00000008820808808800008200208820000000800208220000028a00008820808200200008a08808220000000020020020a00200808020000820008800020200820200008008208220000828020020820200020828008020808208808200020800220020220200800a20000008800208000020020220208028028008000808200000000a20208000008228220000028000020a20000008800008200a00820028208800208200800008800000828820208200208a00000000800800a00028020220000200000200220000220808000000a00000808000820a08008800008820008008008200800200028000020220800800808200220808800000200020000228028020000800a20000208800a00a00800008000008020808200020200a00000020800a08000828208020800000008020200800020008220800a00008800008820800808800208220200000808000000a00020028008020008a20000228000000808000020020008228020200a00200028808208800008008000200220208808028200000808828008028200000a00000028000000020800020200a08000820008800800a08008220020808008820028000208820028000020200a00020020800a08820020008000000008808200200800208008208a00000a28028200820800208000020a20008808000200a20000200028008200208800820200220800220800020800800000808020a00200028828000000a08008020220800000020800008a00200a08028008800008800020208220800820808220220208000820028800200a00020200800008a00820200200000000820008800a08800000028020208020000020020800228800220800008228028020000800808820008000008208020228200200820008000020a00020000000800a00220808008200008a20800200200208200000220000000a20020008820008808820220000208800020008800a08220028028220208200808028220000a08000200020800020000020000a00028020028020008000000208820200828800208020000808000028200208000008020020008800808200220808208828028000000208808000800a08200020228800008028028000a00000220008020a00a00820028200020000800808000220a08028800020200000008020220000a00000820000020200820828200820208208028008020a08200800020220808a00000200800808028020200200a00820800208820200008800008200000020008008800008200028028220a08800820208200808800000020a20000208020220800200a28828000800000008020220820000008828008a00008a08000020a20800a20808208200000008800200800208200028200200000228800020020200808800208000000820828008220000808008000a00a08820800228020808228008020800200208020000000800220028228800000808000220a00008008008200820a08a00020000820808000820028000008a20800200a00008208820000a00200208000200820200a00800000020208028028200a00a00a08020000020000a20008228000800828008200020a00000828208a00200000800008800a08a08800020220008028800200a00008220008028200000820808020220800228008000820808220800200a00800a00828228020800808000028a20200020000208000a00028028008800a08820828000000800a28000020220208008820028800000200028020000208800820020220008808028000000a08220008008020208200808000220808220008000a20a00200800220200a00828808228820808a00800200220200028008000020a08808020000800000220808008220008208008220a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac

private abbrev plane := Astra247824.CompactWeights.plane

private def trialAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => Nat.minFacAux n k
  | fuel+1, k => if n < k*k then n else if k ∣ n then k else trialAux n fuel (k+2)

private theorem trialAux_eq (n fuel k : ℕ) : trialAux n fuel k = Nat.minFacAux n k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [trialAux, Nat.minFacAux]
    split <;> try rfl
    split <;> try rfl
    exact ih _

private def least (n : ℕ) : ℕ := if 2 ∣ n then 2 else trialAux n 105 3

private theorem least_eq (n : ℕ) : least n = n.minFac := by
  simp only [least, trialAux_eq, Nat.minFac]

private def tag (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => tag d k + if (plane k).testBit d then 2^k else 0

private theorem tag_lt (d k : ℕ) : tag d k < 2^k := by
  induction k with
  | zero => simp [tag]
  | succ k ih =>
    rw [tag, pow_succ]
    split <;> omega

private def greater : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, p => if p < 2^k then plane k ||| greater k p
    else plane k &&& greater k (p-2^k)

private theorem greater_spec (k p d : ℕ) :
    (greater k p).testBit d = true ↔ p < tag d k := by
  induction k generalizing p with
  | zero => simp [greater, tag]
  | succ k ih =>
    have bound := tag_lt d k
    by_cases small : p < 2^k <;> cases bit : (plane k).testBit d <;>
      simp [greater, tag, small, Nat.testBit_or, Nat.testBit_and, bit, ih] <;> omega

/- Signed denominator masks, shared by full blocks and within-block tails. -/
def denomWords (p : ℕ) : ℕ × ℕ :=
  (primeWord, if 256 ≤ p then 0 else greater 8 p)

private theorem negative_spec (p d : ℕ) :
    (denomWords p).2.testBit d = true ↔ p < tag d 8 := by
  have bound := tag_lt d 8
  change tag d 8 < 256 at bound
  by_cases big : 256 ≤ p
  · simp [denomWords, big]; omega
  · simp [denomWords, big, greater_spec]

private noncomputable def valid (d : ℕ) : Bool :=
  if d ≤ 29 ∨ 43399 < d then true else
    let q := least d
    let m := Ordinary.mu 16 d
    let t := tag d 8
    if primeWord.testBit d then (q == d) && (m == -1) && (t == 0)
    else if t = 0 then decide (q ≤ 29) || (m == 0)
    else (t == q) && (m == 1)

private def tree (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, lo => f lo
  | k+1, lo => tree f k lo && tree f k (lo+2^k)

private theorem tree_get {f : ℕ → Bool} {k lo : ℕ} (ok : tree f k lo = true)
    {d : ℕ} (low : lo ≤ d) (high : d < lo+2^k) : f d = true := by
  induction k generalizing lo with
  | zero =>
    simp only [pow_zero] at high
    have e : lo = d := by omega
    subst d
    exact ok
  | succ k ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ok
    rw [pow_succ] at high
    by_cases left : d < lo+2^k
    · exact ih a low left
    · exact ih b (by omega) (by omega)

private theorem join {f : ℕ → Bool} {k lo : ℕ} (a : tree f k lo = true)
    (b : tree f k (lo+2^k) = true) : tree f (k+1) lo = true := Bool.and_eq_true_iff.mpr ⟨a,b⟩


set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_0 : PLift (tree valid 9 0 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_1 : PLift (tree valid 9 512 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_2 : PLift (tree valid 9 1024 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_3 : PLift (tree valid 9 1536 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_4 : PLift (tree valid 9 2048 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_5 : PLift (tree valid 9 2560 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_6 : PLift (tree valid 9 3072 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_7 : PLift (tree valid 9 3584 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_8 : PLift (tree valid 9 4096 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_9 : PLift (tree valid 9 4608 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_10 : PLift (tree valid 9 5120 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_11 : PLift (tree valid 9 5632 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_12 : PLift (tree valid 9 6144 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_13 : PLift (tree valid 9 6656 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_14 : PLift (tree valid 9 7168 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_15 : PLift (tree valid 9 7680 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_16 : PLift (tree valid 9 8192 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_17 : PLift (tree valid 9 8704 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_18 : PLift (tree valid 9 9216 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_19 : PLift (tree valid 9 9728 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_20 : PLift (tree valid 9 10240 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_21 : PLift (tree valid 9 10752 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_22 : PLift (tree valid 9 11264 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_23 : PLift (tree valid 9 11776 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_24 : PLift (tree valid 9 12288 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_25 : PLift (tree valid 9 12800 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_26 : PLift (tree valid 9 13312 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_27 : PLift (tree valid 9 13824 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_28 : PLift (tree valid 9 14336 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_29 : PLift (tree valid 9 14848 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_30 : PLift (tree valid 9 15360 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_31 : PLift (tree valid 9 15872 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_32 : PLift (tree valid 9 16384 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_33 : PLift (tree valid 9 16896 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_34 : PLift (tree valid 9 17408 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_35 : PLift (tree valid 9 17920 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_36 : PLift (tree valid 9 18432 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_37 : PLift (tree valid 9 18944 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_38 : PLift (tree valid 9 19456 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_39 : PLift (tree valid 9 19968 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_40 : PLift (tree valid 9 20480 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_41 : PLift (tree valid 9 20992 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_42 : PLift (tree valid 9 21504 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_43 : PLift (tree valid 9 22016 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_44 : PLift (tree valid 9 22528 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_45 : PLift (tree valid 9 23040 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_46 : PLift (tree valid 9 23552 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_47 : PLift (tree valid 9 24064 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_48 : PLift (tree valid 9 24576 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_49 : PLift (tree valid 9 25088 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_50 : PLift (tree valid 9 25600 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_51 : PLift (tree valid 9 26112 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_52 : PLift (tree valid 9 26624 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_53 : PLift (tree valid 9 27136 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_54 : PLift (tree valid 9 27648 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_55 : PLift (tree valid 9 28160 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_56 : PLift (tree valid 9 28672 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_57 : PLift (tree valid 9 29184 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_58 : PLift (tree valid 9 29696 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_59 : PLift (tree valid 9 30208 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_60 : PLift (tree valid 9 30720 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_61 : PLift (tree valid 9 31232 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_62 : PLift (tree valid 9 31744 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_63 : PLift (tree valid 9 32256 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_64 : PLift (tree valid 9 32768 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_65 : PLift (tree valid 9 33280 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_66 : PLift (tree valid 9 33792 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_67 : PLift (tree valid 9 34304 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_68 : PLift (tree valid 9 34816 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_69 : PLift (tree valid 9 35328 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_70 : PLift (tree valid 9 35840 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_71 : PLift (tree valid 9 36352 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_72 : PLift (tree valid 9 36864 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_73 : PLift (tree valid 9 37376 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_74 : PLift (tree valid 9 37888 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_75 : PLift (tree valid 9 38400 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_76 : PLift (tree valid 9 38912 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_77 : PLift (tree valid 9 39424 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_78 : PLift (tree valid 9 39936 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_79 : PLift (tree valid 9 40448 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_80 : PLift (tree valid 9 40960 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_81 : PLift (tree valid 9 41472 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_82 : PLift (tree valid 9 41984 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_83 : PLift (tree valid 9 42496 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_84 : PLift (tree valid 9 43008 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_85 : PLift (tree valid 9 43520 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_86 : PLift (tree valid 9 44032 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_87 : PLift (tree valid 9 44544 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_88 : PLift (tree valid 9 45056 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_89 : PLift (tree valid 9 45568 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_90 : PLift (tree valid 9 46080 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_91 : PLift (tree valid 9 46592 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_92 : PLift (tree valid 9 47104 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_93 : PLift (tree valid 9 47616 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_94 : PLift (tree valid 9 48128 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_95 : PLift (tree valid 9 48640 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_96 : PLift (tree valid 9 49152 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_97 : PLift (tree valid 9 49664 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_98 : PLift (tree valid 9 50176 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_99 : PLift (tree valid 9 50688 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_100 : PLift (tree valid 9 51200 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_101 : PLift (tree valid 9 51712 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_102 : PLift (tree valid 9 52224 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_103 : PLift (tree valid 9 52736 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_104 : PLift (tree valid 9 53248 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_105 : PLift (tree valid 9 53760 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_106 : PLift (tree valid 9 54272 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_107 : PLift (tree valid 9 54784 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_108 : PLift (tree valid 9 55296 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_109 : PLift (tree valid 9 55808 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_110 : PLift (tree valid 9 56320 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_111 : PLift (tree valid 9 56832 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_112 : PLift (tree valid 9 57344 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_113 : PLift (tree valid 9 57856 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_114 : PLift (tree valid 9 58368 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_115 : PLift (tree valid 9 58880 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_116 : PLift (tree valid 9 59392 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_117 : PLift (tree valid 9 59904 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_118 : PLift (tree valid 9 60416 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_119 : PLift (tree valid 9 60928 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_120 : PLift (tree valid 9 61440 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_121 : PLift (tree valid 9 61952 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_122 : PLift (tree valid 9 62464 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_123 : PLift (tree valid 9 62976 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_124 : PLift (tree valid 9 63488 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_125 : PLift (tree valid 9 64000 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_126 : PLift (tree valid 9 64512 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk9_127 : PLift (tree valid 9 65024 = true) := ⟨by decide +kernel⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_0 : PLift (tree valid 10 0 = true) := ⟨join chunk9_0.down chunk9_1.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_1 : PLift (tree valid 10 1024 = true) := ⟨join chunk9_2.down chunk9_3.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_2 : PLift (tree valid 10 2048 = true) := ⟨join chunk9_4.down chunk9_5.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_3 : PLift (tree valid 10 3072 = true) := ⟨join chunk9_6.down chunk9_7.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_4 : PLift (tree valid 10 4096 = true) := ⟨join chunk9_8.down chunk9_9.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_5 : PLift (tree valid 10 5120 = true) := ⟨join chunk9_10.down chunk9_11.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_6 : PLift (tree valid 10 6144 = true) := ⟨join chunk9_12.down chunk9_13.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_7 : PLift (tree valid 10 7168 = true) := ⟨join chunk9_14.down chunk9_15.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_8 : PLift (tree valid 10 8192 = true) := ⟨join chunk9_16.down chunk9_17.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_9 : PLift (tree valid 10 9216 = true) := ⟨join chunk9_18.down chunk9_19.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_10 : PLift (tree valid 10 10240 = true) := ⟨join chunk9_20.down chunk9_21.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_11 : PLift (tree valid 10 11264 = true) := ⟨join chunk9_22.down chunk9_23.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_12 : PLift (tree valid 10 12288 = true) := ⟨join chunk9_24.down chunk9_25.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_13 : PLift (tree valid 10 13312 = true) := ⟨join chunk9_26.down chunk9_27.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_14 : PLift (tree valid 10 14336 = true) := ⟨join chunk9_28.down chunk9_29.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_15 : PLift (tree valid 10 15360 = true) := ⟨join chunk9_30.down chunk9_31.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_16 : PLift (tree valid 10 16384 = true) := ⟨join chunk9_32.down chunk9_33.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_17 : PLift (tree valid 10 17408 = true) := ⟨join chunk9_34.down chunk9_35.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_18 : PLift (tree valid 10 18432 = true) := ⟨join chunk9_36.down chunk9_37.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_19 : PLift (tree valid 10 19456 = true) := ⟨join chunk9_38.down chunk9_39.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_20 : PLift (tree valid 10 20480 = true) := ⟨join chunk9_40.down chunk9_41.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_21 : PLift (tree valid 10 21504 = true) := ⟨join chunk9_42.down chunk9_43.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_22 : PLift (tree valid 10 22528 = true) := ⟨join chunk9_44.down chunk9_45.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_23 : PLift (tree valid 10 23552 = true) := ⟨join chunk9_46.down chunk9_47.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_24 : PLift (tree valid 10 24576 = true) := ⟨join chunk9_48.down chunk9_49.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_25 : PLift (tree valid 10 25600 = true) := ⟨join chunk9_50.down chunk9_51.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_26 : PLift (tree valid 10 26624 = true) := ⟨join chunk9_52.down chunk9_53.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_27 : PLift (tree valid 10 27648 = true) := ⟨join chunk9_54.down chunk9_55.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_28 : PLift (tree valid 10 28672 = true) := ⟨join chunk9_56.down chunk9_57.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_29 : PLift (tree valid 10 29696 = true) := ⟨join chunk9_58.down chunk9_59.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_30 : PLift (tree valid 10 30720 = true) := ⟨join chunk9_60.down chunk9_61.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_31 : PLift (tree valid 10 31744 = true) := ⟨join chunk9_62.down chunk9_63.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_32 : PLift (tree valid 10 32768 = true) := ⟨join chunk9_64.down chunk9_65.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_33 : PLift (tree valid 10 33792 = true) := ⟨join chunk9_66.down chunk9_67.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_34 : PLift (tree valid 10 34816 = true) := ⟨join chunk9_68.down chunk9_69.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_35 : PLift (tree valid 10 35840 = true) := ⟨join chunk9_70.down chunk9_71.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_36 : PLift (tree valid 10 36864 = true) := ⟨join chunk9_72.down chunk9_73.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_37 : PLift (tree valid 10 37888 = true) := ⟨join chunk9_74.down chunk9_75.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_38 : PLift (tree valid 10 38912 = true) := ⟨join chunk9_76.down chunk9_77.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_39 : PLift (tree valid 10 39936 = true) := ⟨join chunk9_78.down chunk9_79.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_40 : PLift (tree valid 10 40960 = true) := ⟨join chunk9_80.down chunk9_81.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_41 : PLift (tree valid 10 41984 = true) := ⟨join chunk9_82.down chunk9_83.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_42 : PLift (tree valid 10 43008 = true) := ⟨join chunk9_84.down chunk9_85.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_43 : PLift (tree valid 10 44032 = true) := ⟨join chunk9_86.down chunk9_87.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_44 : PLift (tree valid 10 45056 = true) := ⟨join chunk9_88.down chunk9_89.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_45 : PLift (tree valid 10 46080 = true) := ⟨join chunk9_90.down chunk9_91.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_46 : PLift (tree valid 10 47104 = true) := ⟨join chunk9_92.down chunk9_93.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_47 : PLift (tree valid 10 48128 = true) := ⟨join chunk9_94.down chunk9_95.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_48 : PLift (tree valid 10 49152 = true) := ⟨join chunk9_96.down chunk9_97.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_49 : PLift (tree valid 10 50176 = true) := ⟨join chunk9_98.down chunk9_99.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_50 : PLift (tree valid 10 51200 = true) := ⟨join chunk9_100.down chunk9_101.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_51 : PLift (tree valid 10 52224 = true) := ⟨join chunk9_102.down chunk9_103.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_52 : PLift (tree valid 10 53248 = true) := ⟨join chunk9_104.down chunk9_105.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_53 : PLift (tree valid 10 54272 = true) := ⟨join chunk9_106.down chunk9_107.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_54 : PLift (tree valid 10 55296 = true) := ⟨join chunk9_108.down chunk9_109.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_55 : PLift (tree valid 10 56320 = true) := ⟨join chunk9_110.down chunk9_111.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_56 : PLift (tree valid 10 57344 = true) := ⟨join chunk9_112.down chunk9_113.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_57 : PLift (tree valid 10 58368 = true) := ⟨join chunk9_114.down chunk9_115.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_58 : PLift (tree valid 10 59392 = true) := ⟨join chunk9_116.down chunk9_117.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_59 : PLift (tree valid 10 60416 = true) := ⟨join chunk9_118.down chunk9_119.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_60 : PLift (tree valid 10 61440 = true) := ⟨join chunk9_120.down chunk9_121.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_61 : PLift (tree valid 10 62464 = true) := ⟨join chunk9_122.down chunk9_123.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_62 : PLift (tree valid 10 63488 = true) := ⟨join chunk9_124.down chunk9_125.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk10_63 : PLift (tree valid 10 64512 = true) := ⟨join chunk9_126.down chunk9_127.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_0 : PLift (tree valid 11 0 = true) := ⟨join chunk10_0.down chunk10_1.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_1 : PLift (tree valid 11 2048 = true) := ⟨join chunk10_2.down chunk10_3.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_2 : PLift (tree valid 11 4096 = true) := ⟨join chunk10_4.down chunk10_5.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_3 : PLift (tree valid 11 6144 = true) := ⟨join chunk10_6.down chunk10_7.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_4 : PLift (tree valid 11 8192 = true) := ⟨join chunk10_8.down chunk10_9.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_5 : PLift (tree valid 11 10240 = true) := ⟨join chunk10_10.down chunk10_11.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_6 : PLift (tree valid 11 12288 = true) := ⟨join chunk10_12.down chunk10_13.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_7 : PLift (tree valid 11 14336 = true) := ⟨join chunk10_14.down chunk10_15.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_8 : PLift (tree valid 11 16384 = true) := ⟨join chunk10_16.down chunk10_17.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_9 : PLift (tree valid 11 18432 = true) := ⟨join chunk10_18.down chunk10_19.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_10 : PLift (tree valid 11 20480 = true) := ⟨join chunk10_20.down chunk10_21.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_11 : PLift (tree valid 11 22528 = true) := ⟨join chunk10_22.down chunk10_23.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_12 : PLift (tree valid 11 24576 = true) := ⟨join chunk10_24.down chunk10_25.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_13 : PLift (tree valid 11 26624 = true) := ⟨join chunk10_26.down chunk10_27.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_14 : PLift (tree valid 11 28672 = true) := ⟨join chunk10_28.down chunk10_29.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_15 : PLift (tree valid 11 30720 = true) := ⟨join chunk10_30.down chunk10_31.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_16 : PLift (tree valid 11 32768 = true) := ⟨join chunk10_32.down chunk10_33.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_17 : PLift (tree valid 11 34816 = true) := ⟨join chunk10_34.down chunk10_35.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_18 : PLift (tree valid 11 36864 = true) := ⟨join chunk10_36.down chunk10_37.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_19 : PLift (tree valid 11 38912 = true) := ⟨join chunk10_38.down chunk10_39.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_20 : PLift (tree valid 11 40960 = true) := ⟨join chunk10_40.down chunk10_41.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_21 : PLift (tree valid 11 43008 = true) := ⟨join chunk10_42.down chunk10_43.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_22 : PLift (tree valid 11 45056 = true) := ⟨join chunk10_44.down chunk10_45.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_23 : PLift (tree valid 11 47104 = true) := ⟨join chunk10_46.down chunk10_47.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_24 : PLift (tree valid 11 49152 = true) := ⟨join chunk10_48.down chunk10_49.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_25 : PLift (tree valid 11 51200 = true) := ⟨join chunk10_50.down chunk10_51.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_26 : PLift (tree valid 11 53248 = true) := ⟨join chunk10_52.down chunk10_53.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_27 : PLift (tree valid 11 55296 = true) := ⟨join chunk10_54.down chunk10_55.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_28 : PLift (tree valid 11 57344 = true) := ⟨join chunk10_56.down chunk10_57.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_29 : PLift (tree valid 11 59392 = true) := ⟨join chunk10_58.down chunk10_59.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_30 : PLift (tree valid 11 61440 = true) := ⟨join chunk10_60.down chunk10_61.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk11_31 : PLift (tree valid 11 63488 = true) := ⟨join chunk10_62.down chunk10_63.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_0 : PLift (tree valid 12 0 = true) := ⟨join chunk11_0.down chunk11_1.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_1 : PLift (tree valid 12 4096 = true) := ⟨join chunk11_2.down chunk11_3.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_2 : PLift (tree valid 12 8192 = true) := ⟨join chunk11_4.down chunk11_5.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_3 : PLift (tree valid 12 12288 = true) := ⟨join chunk11_6.down chunk11_7.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_4 : PLift (tree valid 12 16384 = true) := ⟨join chunk11_8.down chunk11_9.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_5 : PLift (tree valid 12 20480 = true) := ⟨join chunk11_10.down chunk11_11.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_6 : PLift (tree valid 12 24576 = true) := ⟨join chunk11_12.down chunk11_13.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_7 : PLift (tree valid 12 28672 = true) := ⟨join chunk11_14.down chunk11_15.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_8 : PLift (tree valid 12 32768 = true) := ⟨join chunk11_16.down chunk11_17.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_9 : PLift (tree valid 12 36864 = true) := ⟨join chunk11_18.down chunk11_19.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_10 : PLift (tree valid 12 40960 = true) := ⟨join chunk11_20.down chunk11_21.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_11 : PLift (tree valid 12 45056 = true) := ⟨join chunk11_22.down chunk11_23.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_12 : PLift (tree valid 12 49152 = true) := ⟨join chunk11_24.down chunk11_25.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_13 : PLift (tree valid 12 53248 = true) := ⟨join chunk11_26.down chunk11_27.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_14 : PLift (tree valid 12 57344 = true) := ⟨join chunk11_28.down chunk11_29.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk12_15 : PLift (tree valid 12 61440 = true) := ⟨join chunk11_30.down chunk11_31.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_0 : PLift (tree valid 13 0 = true) := ⟨join chunk12_0.down chunk12_1.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_1 : PLift (tree valid 13 8192 = true) := ⟨join chunk12_2.down chunk12_3.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_2 : PLift (tree valid 13 16384 = true) := ⟨join chunk12_4.down chunk12_5.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_3 : PLift (tree valid 13 24576 = true) := ⟨join chunk12_6.down chunk12_7.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_4 : PLift (tree valid 13 32768 = true) := ⟨join chunk12_8.down chunk12_9.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_5 : PLift (tree valid 13 40960 = true) := ⟨join chunk12_10.down chunk12_11.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_6 : PLift (tree valid 13 49152 = true) := ⟨join chunk12_12.down chunk12_13.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk13_7 : PLift (tree valid 13 57344 = true) := ⟨join chunk12_14.down chunk12_15.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk14_0 : PLift (tree valid 14 0 = true) := ⟨join chunk13_0.down chunk13_1.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk14_1 : PLift (tree valid 14 16384 = true) := ⟨join chunk13_2.down chunk13_3.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk14_2 : PLift (tree valid 14 32768 = true) := ⟨join chunk13_4.down chunk13_5.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk14_3 : PLift (tree valid 14 49152 = true) := ⟨join chunk13_6.down chunk13_7.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk15_0 : PLift (tree valid 15 0 = true) := ⟨join chunk14_0.down chunk14_1.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk15_1 : PLift (tree valid 15 32768 = true) := ⟨join chunk14_2.down chunk14_3.down⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private def chunk16_0 : PLift (tree valid 16 0 = true) := ⟨join chunk15_0.down chunk15_1.down⟩

/- Under the hard-edge bounds, the two bits give the exact signed Möbius weight. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem denomWords_correct {p d : ℕ}
    (pp : p.Prime) (hlarge : 23 < p) (_hcap : p ≤ 3006) (hpd : p < d) (hdy : d ≤ 43399) :
    ((if (denomWords p).1.testBit d then (1 : ℤ) else 0) -
     (if (denomWords p).2.testBit d then (1 : ℤ) else 0)) =
     (if p < d.minFac then -moebius d else 0) := by
  have pl : 29 ≤ p := by
    by_contra! h
    have small : ∀ i : Fin 29, 23 < i.val → ¬i.val.Prime := by decide +kernel
    exact small ⟨p,h⟩ hlarge pp
  have ok := tree_get chunk16_0.down (d := d) (Nat.zero_le _) (by change d < 65536; omega)
  have inRange : ¬(d ≤ 29 ∨ 43399 < d) := by omega
  simp only [valid, if_neg inRange, least_eq, Ordinary.mu_eq] at ok
  change (if primeWord.testBit d then (1:ℤ) else 0) - _ = _
  rw [if_congr (negative_spec p d) rfl rfl]
  cases bit : primeWord.testBit d with
  | true =>
    simp [bit] at ok
    obtain ⟨⟨q,m⟩,t⟩ := ok
    simp [q,m,t,hpd]
  | false =>
    by_cases t : tag d 8 = 0
    · simp [bit,t] at ok
      rcases ok with q | m
      · simp [t,show ¬p < d.minFac by omega]
      · simp [t,m]
    · simp [bit,t] at ok
      obtain ⟨q,m⟩ := ok
      by_cases a : p < d.minFac <;> simp [q,m,a]

end Astra247824.HardTail


/- Cached exact prime ranks and sparse composite-rank lookups for the complete blocks. -/
namespace Astra247824.FullLookup

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
def rawPattern (p : ℕ) := ((1 <<< (p*(65536/p+2)))-1)/((1 <<< p)-1)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
theorem rawPattern_eq (p : ℕ) : rawPattern p = fixedPattern p 65536 := by simp [rawPattern,fixedPattern,Nat.shiftLeft_eq]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
abbrev negative := Astra247824.CompactWeights.negative
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base29 : {w : ℕ // CompactWeights.unpackRanks 12 4 679 0 0x746333346425731425262404356254348222563426545248862535524442453355245265240577324574363664313452563252433533363355527246653325275055653545227143476346263224428342255336423415314457462462654422545426363354444445523652361522457634421246434462524225534373555352551363714444723354335635343245444526562364422523254244834242446334237444451133443432534624334182365362443242556243331442544538254363523343524334444321734333372254442644254162316432334344363062152655263334331733335613423443321344233442325446215423263355123543243315335232540343424333311526341442342343222273241542313323450305236403224321331522034243203241613132231221322232223122122310321112112011110110100000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base31 : {w : ℕ // CompactWeights.unpackRanks 12 4 679 0 0x646333346325631325162404356254348221562326544237852524523431453355244265230577224464353654213452463242423433362355427245553325275054652535226142475335253224428332244336313415214347462352644322545325363254344344523652261422356634321236433452524225533362545352541253614444713354225525343135444426561364422422254143833242345324227443451123442432524623333172365252433232446243231442434437253263423243523333344221634332362254442633254161315422333334353062142545163324321633225613313442321243233342224445214423163244123533233315334221530343423333201426231432332333222163231431313322450304135303223221231421024232203230612122231220311221213112112210211012002001100000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base37 : {w : ℕ // CompactWeights.unpackRanks 12 4 679 0 0x636332346324531325162404346244347221462316534226842524523430453245244254230576223364353544212442463241423333352354426235553325265044642525225142474335243124428332244235212415214346451342644322445325253243344343423652251422346634321135433442424125532352544351541243614434712354224525333125344426551264322322144143823242344223227343341122441432523622323162355252423231446243231332434436253162423233423332344221533231362244432623243161314322333234352052142445062324221533224612312342321143133342223444113423163234123522223314234121520333423322201325131332332323222153130331313212440303125302222121231311023222203230511112121120310221112111012110101011001000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base41 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x33cd17335232cc3940dbca36fa46648eaa25bc54ca5c4256a54e2ad313d49bb1d76345469e6a189b6dc4e38aa76d6d45608f45554a18a76d5311522e9a52271150c4639a50e1d232a3acd55a6d48db896a943126f671225d89c89a84d8d3aac6a9aca8b16dce52b129544d855b90e94ab194d23198f96a17214d2ea36c94a431a89649a63272a8a26597328932da6e359467269a4da6d1722462699752922553511c5189269a51d4222d47064d428c6d298a4526992632db69271b2544c569b29c4916cc49946209385b4900d52cb45b29349188b0996192a30c20ab08a2512c324269141162020a281411051209201240200200000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base43 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x2bcd172b51b2cb3930dac9b6fa46548daa15b454ba5c41d6a44daad313d49b91555b45469e4996936dc4e36aa76c4d33608f33554a16a76d4311522c9952251050b4637a40e0d222a38cd5596d489b895a942d26b571225c85c85a80c893aac4a9aca6714dcc528d291449855b70e70aad94923196f94a17214d2c636c949c3126964924327228a265152a6932d26db55462a69a4926d16e245a65974a91a5134d1c1188a6924d54222946c64d428b69194a45269826329a6526da2534c469a29c4886cb49045a0938534900cc2c245b28a49088a09161129a0c20a20892492c324248920941820a081209049001200040000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base47 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x2bc917234db2cb3930daa9a6b946548da9956c50ba5c41c6a44d98d20fd49b6d555b44c69e4916936dc2e26aa72c2d31608eb31546169f6d3311521c994e251030b45b79c0a0d2229b6cd3594d385b8958942d266d6d225485465a60c693aac2a98c26694d4c528ca90c49855b70d6caad948a3116b94a07194d2a636c945b2d249648a42a6e28996515224932d16db51442a69248a6916da45265954a7194d34d1a1168a6924d441928c6c64d408b69170a25249025b2996516da2522c449925c2886cb45045a05284a4900cb0c225b24a29068a0496112590c109a089249282202249009410209041200041000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base53 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x2bc9151b4db2ca3930da89a6b946448ca9952c4cba5441c4a42d96d20bd49b4d555b24c69d4916926dc2da6a97242d31606e331446149e6933114e1c994e14d010b41b7930a0b2225b6cd3514d265b85588c2d266c6d125485465a604493aac2a18c16614d4c126ca90b49855b6cd4c2a9948a1116792a06d84d2a6268945b29249548942a6a28916495214930d16d351342249248a49169a45265950a5114934d1a1164a69249341128b6864cc08a69150a25228825a2914506da25228449925b08848b45045105264a45008b08225304a2904820486092590c1092048241081202241008408208001000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base59 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x2ba914db4db28a3930d289a679464484a995244caa5341c4a42d14d20b549a4d451b24c69549169269b2d26a95242921606a330c46149e4932d04e1a994d94d010a41b7530a0b2225b68c3514d265385568b2d266b6d025484c65a604453a6b2998c16594d3c116ca70349855a68d4c2a9148a1096712a06984caa5a68925b25249544942269a6916494e148b0d16d351242145228a49169a4126595093112934c981160a69149321128b6454cc04a48950225228821a2914504d224928449921308828b44841105164a24808b08121304928848204860825808104a040241041201240008200200000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base61 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x2b8914da4db28a3530d285a67145c484a994e34caa1341b4a32914d20ad49a4d451224b69545169165b2ca6a93242921586a22cc46049e4532d04d9a992d94d010a41b7120a0b2225368c1512d265365468b2d166b6d024c84445a40445386b259881658493c116c250349855268d482a5148a0c96692986982caa5268921b2514944094226926914494e148b09169251142145228a29169a40a4585092d029348981060a49149320908b60548b04948950224a28821a28925029224928345921208808b24840905140a24808a041212041288482048408050040049040240041001040000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base67 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x238892da4db2893530d28596694544848994db2caa1241b4632914d10ad4922d450a24b49545169065b28a6a932429215849a2cc46049d453290499a992994c810a4137120a0b2125264c1112d261365448b0d16634d024c84341a40445286b259681458493a116c150249851268c482a5128a0c16610986982c9a5264921b25149420921a68a6914494e144b0916914d141945208229149a4024584c92d029244981040a28948b20908b60448b0494884c220a08821a28105028a24924341921108804b04840904920a240089041212041248441048200048040041040200001000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base71 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x238812da49a28934b0d26596694534848912db2c9a124134632914910ac4922d450a24b49444969065b2896a92e428a1584992cb46049d253290499a592912c80ca4136d20a092105264b0d12d261345348b0d165b4d024b84241a40425286a2586814504938116c14c249831248b482a512820c14610986982c985244121a25149420921268a6914412e124b0906514d121944a08225149a4022504c929025224961040a28944b20908b60344b0092884c220904821a08104828924920341900908804b00820904120924008904120a040208400048000048000040040000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base73 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x228812d249a28930b0d24516694134846912db2c981240b4632914910ac49129450a24b4934496886532896a82e408a1584592cb46049c252288491a592902c80c24126d209872105264a0c92d261341348b0c965a4d024b64241940325286225864145048b81168148229831248a482a492820c146109069028981244121a2514542092126496912412d920b0904514c921940a0822514594022484c125021224961040928944b20904a60244300928848120904021a04104028904920241100908800a008201040209240089040209000200200008000040000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base79 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x226812d229a28930b0d24516612134846912da2c981140b2632914510a449129430a24b49344868844b2886a82e404a1584192c346045b2522884918512902c80c14126d20586e10526490c92d161321348a0c96524d024b44241920321186225864125048a81168148229811244a282a092820c146108869028980a4012122514132092116496892412d120b0904492c921920a0412512594022484c025021224960820924924b20904a401443001288441201040212041000089049202209009080009008201040209040048040008000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base83 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x224812d229a28830b0d14514612134836910da2c980940b2632914490a348929330a24b4534486484432886a02a404a1584110c346045b2122884908512502c80c04126d10584e10524490c90d161320b48a0c165149024b44241120320986225864125028a80948144229811244a2828092820c126008849028960940120a25140b2092096496892402c920b05044828921120a0412512514022484c021001220940820924920a20904940144200108844100104000a041000088041202201008080009008201000201000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base89 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x1a4812d225a28830b0d144946100b4834910da2c880940a26325144906328929330a2434134486484422886a029c0491584110c246045a2120884908112502880c04124d10584a104a4090c90d161220b4890c165149024b44141100220982225864125028a6094814422900d24422828082420c125808848828960140120a25120a20920864964904028920b05044828121120a0412502494012404c0210012008408208249209209009401402001080241001040002001000048040202201008080001008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base97 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x1a4810d225228830a0c944946100b4432910da2c880920a26325124905b2892933022434124486084422806a029b0491584100c246025a2110804908112502480c040a4d10584a104a4080c90914122034890c165149024a44141100220881a25844125024a4094814022900ca4422818082420c125004848828160120020a24920a20920864944904028920b04840828020920a04125020920124048021000a008208208241209208001401402001040041001000001001000048040202001000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base101 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x1a4810d225128030a0c944945900b4432900da28880920a25b25124805b2492933012434122486084422406a02930491182100c246025a0110804508112502480c04094d10504610494080c90914122034490c165149020a24140900220861925844105024a4014814012900ca4422808002420c105004044828140120020a24920920920864944900024920a04040828020920200125020120124028020800a008008208201009208001401201001040001000000001001000048000201000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base103 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x124410d22512802ca0c944945100b4032900da24880920925b24924805a2492932c12434122406084412406982530491182100824602590110804508112502080c02084d10104610494080c90912122034490c145049020224140800120861905844104824a4012814012900ca2412808002020c004804040828140120020a04920920920864844100020900a040408280008202001210201200240240208009008008008001009208001200201001000000000000001001000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base107 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x124410922510802ca0c940945100a4032880da2486092092532492480592492932812432112406084412404982530411182100824602590090802506112482080c02084d10104590494080c908920a2032490c144848820224120800120061905824104824a4012412012900c22412406002010c004804040828040120020a04920820120860824100020900a000208280000202001010200200240200208008000008008001008200001200001000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base109 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x114410922510402ca0c840944900a4030880da2406092092530492480512492532412432112406004412402982530411182100822602510010802106112482080c02082d101045904940008908900a20324108144848800224120000120041905824104820a2012412002900822012404002010c004804020828040120020a009008200200608241000208009000208240000201001008200200040200200000000008008000000200001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base113 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x1044108a25104028a0c840924900a4030800da2404092082520492480512490532412422112406004412402980530401102100422602510010802106092482080c02080d001045104940004904900a20224108144048800204120000120041105024104800a2002402002880822012404002000c0048040208280201000209001008200200608040000208001000208200000001001000200200000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base127 : {w : ℕ // CompactWeights.unpackRanks 12 3 679 0 0x104410892510402890c840924900a4030800d224040120025204124805124905324124220924060044124029004b0401082100422582490010802086092482000c020809001045104940000900900a20220108140044800200120000120041105020104800a2002402002480422012002002000c0048040008080201000009001008000200408040000008001000008000000001001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base131 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x49125591065348455058220395081405a115419151b515245108091406817003448124c55011044c5504030442804951580040505414120809402014001008918411406001040140241404040200410041041000101000040801000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base137 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x49115551061348455058220391081405a115015151a515244104091405817002448124855011044c5100030441804851180000505414120805402014001008514411005001040140201004040100410001040000100000040400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base139 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x45115451061348455058120391081404a015011151a50514410405140580700244412485501100485100020441400851080000505414110805402014000004514010005001040100101004000100400000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base149 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x451154510512484540581202900814049015011051a50504410405140540600244402485100100445100020441400451080000505410100805001014000004510000005000040100001000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base151 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x451150500512084540541102900804049014011051950504410405040140600204401481100000445100020441000451080000501400100404001014000000500000004000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base157 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x451150400112084500541101900804009014011051910404410401040100500200401481100000441100020441000441040000100400100404000010000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base163 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x451110400111084500501101900804005004011051510400400401000100500200401441100000441100010401000040040000100400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base167 : {w : ℕ // CompactWeights.unpackRanks 12 2 679 0 0x451010400110084500501101800404005000011011410400000401000100500100401441100000401000010000000040040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base173 : {w : ℕ // CompactWeights.unpackRanks 12 1 679 0 0x2d12050a831460801001164800800430421840000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base179 : {w : ℕ // CompactWeights.unpackRanks 12 1 679 0 0x29020502821060001001160800800420021000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base181 : {w : ℕ // CompactWeights.unpackRanks 12 1 679 0 0x21020102001020001001060800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base191 : {w : ℕ // CompactWeights.unpackRanks 12 1 679 0 0x1000102001000001001040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base193 : {w : ℕ // CompactWeights.unpackRanks 12 1 679 0 0x102000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base197 : {w : ℕ // CompactWeights.unpackRanks 12 1 679 0 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def base199 : {w : ℕ // CompactWeights.unpackRanks 12 1 0 0 0x0 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
def bases : ℕ → ℕ
  | 29 => base29.1
  | 31 => base31.1
  | 37 => base37.1
  | 41 => base41.1
  | 43 => base43.1
  | 47 => base47.1
  | 53 => base53.1
  | 59 => base59.1
  | 61 => base61.1
  | 67 => base67.1
  | 71 => base71.1
  | 73 => base73.1
  | 79 => base79.1
  | 83 => base83.1
  | 89 => base89.1
  | 97 => base97.1
  | 101 => base101.1
  | 103 => base103.1
  | 107 => base107.1
  | 109 => base109.1
  | 113 => base113.1
  | 127 => base127.1
  | 131 => base131.1
  | 137 => base137.1
  | 139 => base139.1
  | 149 => base149.1
  | 151 => base151.1
  | 157 => base157.1
  | 163 => base163.1
  | 167 => base167.1
  | 173 => base173.1
  | 179 => base179.1
  | 181 => base181.1
  | 191 => base191.1
  | 193 => base193.1
  | 197 => base197.1
  | 199 => base199.1
  | _ => 0
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc0 : {w : ℕ // CompactWeights.unpackRanks 13 2 256 0 0x4110110100114404110500500404404110410104500410004510004014414104100504510010014500504110414014110004514404110510504114414114516 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc1 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 97 0x328244940928845005a05a04361821028a45244221128325841a4c9099212018 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc2 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 172 0x110412d841344b4084022480004c169960108264a0892110c009224b4026184c = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc3 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 242 0x430916912006030092086d204044108348049221821a0034802132ca05144a4 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc4 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 309 0x265108040029104a04904a69025320060a48b0116022500100886980c10d8242 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc5 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 375 0x1208a0510c001928104224844029128101a60840a2184d12d24584082880c100 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc6 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 439 0x6106132c24110036880802406030c141949300041b0022890520d00080c20094 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc7 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 502 0x304809801325820040141965008a0434086012810c80124422902c101244a408 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc8 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 564 0x124404830016902180494806082402122184000890c32186190800806812c041 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc9 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 623 0x49304a0110406194902c244b04240824200040a0cb4004402980410484996020 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc10 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 685 0x4000422920014c160164009a41a4492000502102480c82002d0082211409000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc11 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 739 0x430882184902522014012000810500480c329941224845000268024229021b4c = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc12 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 801 0x2020104402990d008800108a0180120022124c84892430426484022916002104 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc13 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 857 0x4400c824004208141120a4494c300025101064808b4010c301800a042618483 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc14 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 916 0xa00940205064a0c32892110ca01900809008008060308308100025221340908 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc15 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 974 0x4114810012422c821204009808001060a44120169020824800a0006820520514 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc16 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1028 0x128a24048340860221005848820001205065000308908008240b40a4012c3080 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc17 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1084 0x941220a40a4024100110982034c001904229000240160864305005008929049 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc18 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1142 0xc00886020906520810000512084090496006c321240900268144021a0080c12 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc19 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1199 0x410082894432004530432006000c000240221901205041904a0910520c0252 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc20 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1254 0x129060140149045024a20044001808304205a00b00044008204b0886080d125 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc21 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1311 0x29140020200b0c20106802506184010010912022180024190132424000422100 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc22 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1362 0x41060308a0080082802910006004404990500520410484080c008a410448 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc23 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1410 0xa2430c101120001a24004b2800c009a0014012184832502484014004d224825 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc24 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1470 0x44201205008848804124a01308248809304244944809028228841a0014090020 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc25 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1526 0x20900110882180014914500482520004092800d8052448201651280002082608 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc26 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1581 0x44220164009860b4c200809120240840808108104224908029060204001940 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc27 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1633 0x5804208001900204200a04a40001005840900a0186000500030896016810086 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc28 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1681 0x105220205144929128101020a04b2000c001a64a0404084020c2451483008012 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc29 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1739 0x420184910c265008908049020821908121128220040a00040825109000944301 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc30 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1795 0x1000048925024821b4000014520d821048060844204040a00921141020844a0 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc31 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1848 0x209821204020009028064800b40000304044940b6800800484030400814920ca = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc32 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1900 0x94400106410010014120800530082980c105000248900840024a00340929000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc33 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 1948 0x8b48044224a0130000804400d064044008121120200248b2100930100494806 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc34 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2002 0x641080410610040640083088090018218001408603280410042099250090418 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc35 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2054 0x1020a0114082080d20c020b00a4904420802434c00882030d800200329060109 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc36 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2111 0x6c100021004000129020224104821044200200800940008301a0420802914 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc37 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2154 0x48b6810532000020422080910824134006012030080004ca010240288012041 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc38 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2206 0x182084480180122180120880814c104221848020000009204904861001209264 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc39 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2257 0x60001840144a0086922500084022080c100804a0834092920804414026102c12 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc40 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2312 0x6014110880584480880000c020304b4106102080400c1010480010642083001 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc41 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2360 0x5348100008104a4580012016800122004012100d109225008120801300045b08 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc42 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2413 0x2124080804880402084510c02814102424184082010820c000b0c308960009a0 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc43 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2466 0x420182024880082420c02400014116c104020000a010690290603049410650 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc44 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2517 0x4329108021804808120024320000940148804304a21904201160320000340261 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc45 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2572 0x21900208008104040804001820124840b04201001009a20244041020104845a0 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc46 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2618 0x209025048829020008261244a0800d12082024896004000c264000b40948205a = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc47 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2676 0x1005024221008a00140324041304008820000800144240120308040a08b49124 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc48 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2725 0x4080802c02002194084016100820114802084820502020020912410004410080 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc49 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2769 0x25808028100000064a44041804024225008360000225221000241909004a408 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc50 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2819 0x510100020822816020804530484080900c80100c801141220204204908148209 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc51 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2871 0x24020a01000828840108244844901021100a20a0016182100902490882004 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc52 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2918 0x4034102930104090092004d00480430c06084822080480400992c3258200489 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc53 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 2975 0x404090006000430c02004c00882500c200048008800101a4120c001024100004 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc54 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3016 0x4001061848209005100a0404896006022100014014894c125065a0002980802 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc55 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3070 0x268905305241304328028120204044a019090000600043089600000211080601 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc56 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3124 0x1240909900200205000968800100820248220045101200a40a0104c009044840 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc57 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3172 0x1064008a0104122c00094002010802122410c34010112404484020110420c84 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc58 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3221 0x121208801a04a49804104020300240041004a0000c94102810102000c8201200 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc59 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3267 0x948824209240000808068108220b00300805001060040120149020061208041 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc60 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3314 0x45000a6804d10180010c24104812000490022900402086130c20890022120004 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc61 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3365 0x20d80104014890100480424016102c008a2000000002d100200a4c10002512c2 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc62 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3414 0x102802106420406006010922590030090422120000010110810c000804801804 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc63 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3460 0x200069024000240821901129800b0014904100182430802994820582580002 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc64 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3512 0x4004114430086000490110c02822420494182032026004020014c001a251 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc65 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3562 0x402c261008840040004a25a0c328901028804244228001029040804b4182420c = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc66 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3619 0x68109320040b0004106120d00000002804c10020004802910402804490030182 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc67 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3666 0x4002016110880424490180402506400024804c30506080422010020c8408448 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc68 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3716 0x524010c109001200800104a2082510982130014000020182100480812400d801 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc69 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3764 0x64009a0010490180000024000000812c028004b4830100020c20504882010810 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc70 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3808 0x60049120224108208805000840900308109200200b448489040210418042410 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc71 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3858 0x84082080d304821008a0912402122004414114420d000a04b09008000024200 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc72 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3908 0x9a01808b0002802100480c22104010120084002884032120120014194830424 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc73 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 3958 0x442240403040600010002013000489081040613483088252290040480408201 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc74 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4007 0x80900402ca05048820064100a24840a0004800102024400102d005240000108 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc75 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4052 0x410092104820104404030890d12026030420190800ca0400002000032c04000 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc76 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4098 0x10820434406012822000010cb08844201a01204948840005805000809048021a = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc77 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4150 0x80020522484c320044108820244240045100045040020904200865000021140 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc78 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4198 0xb40001000a44000000920020a40200a0890c00d04124004006402802510080 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc79 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4240 0x2124004814102c825208101144100021a000000610082448040418411250410 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc80 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4289 0x102100030432002422000100824810d221825808261028000a00944049008020 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc81 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4337 0x60869204044a4404190002880090c00884000482114812992810002500c90104 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc82 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4391 0x14096912800d24120420910112180080416082930820110002090c201005a040 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc83 : {w : ℕ // CompactWeights.unpackRanks 13 1 256 4446 0x102104884890030000520c220029024044844268921009800100209820020021 = w} := ⟨_, by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pc84 : {w : ℕ // CompactWeights.unpackRanks 13 1 196 4495 0x6400000010c80110420020404820804402020420014182012 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
def negRank (bits pre n : ℕ) :=
  let q := n/64
  ((pre >>> (12*q)) &&& 4095) + GlobalRank.pop64 ((bits >>> (64*q)) &&& ((1 <<< (n%64+1))-1))

/- Small pages of inclusive prime ranks at odd positions, checked against the dense prime table. -/
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def primePage (q : ℕ) : ℕ := (#[pc0.1,pc1.1,pc2.1,pc3.1,pc4.1,pc5.1,pc6.1,pc7.1,pc8.1,pc9.1,pc10.1,pc11.1,pc12.1,pc13.1,pc14.1,pc15.1,pc16.1,pc17.1,pc18.1,pc19.1,pc20.1,pc21.1,pc22.1,pc23.1,pc24.1,pc25.1,pc26.1,pc27.1,pc28.1,pc29.1,pc30.1,pc31.1,pc32.1,pc33.1,pc34.1,pc35.1,pc36.1,pc37.1,pc38.1,pc39.1,pc40.1,pc41.1,pc42.1,pc43.1,pc44.1,pc45.1,pc46.1,pc47.1,pc48.1,pc49.1,pc50.1,pc51.1,pc52.1,pc53.1,pc54.1,pc55.1,pc56.1,pc57.1,pc58.1,pc59.1,pc60.1,pc61.1,pc62.1,pc63.1,pc64.1,pc65.1,pc66.1,pc67.1,pc68.1,pc69.1,pc70.1,pc71.1,pc72.1,pc73.1,pc74.1,pc75.1,pc76.1,pc77.1,pc78.1,pc79.1,pc80.1,pc81.1,pc82.1,pc83.1,pc84.1] : Array ℕ)[q]!

set_option maxRecDepth 32768 in
private def primeSlab0 : {w : ℕ // (pc0.1 ||| ((pc1.1 ||| ((pc2.1 ||| ((pc3.1 ||| ((pc4.1 ||| ((pc5.1 ||| ((pc6.1 ||| ((pc7.1 ||| ((pc8.1 ||| ((pc9.1 ||| ((pc10.1 ||| ((pc11.1 ||| ((pc12.1 ||| ((pc13.1 ||| ((pc14.1 ||| ((pc15.1 ||| ((pc16.1 ||| ((pc17.1 ||| ((pc18.1 ||| ((pc19.1 ||| ((pc20.1 ||| ((pc21.1 ||| ((pc22.1 ||| ((pc23.1 ||| ((pc24.1 ||| ((pc25.1 ||| ((pc26.1 ||| ((pc27.1 ||| ((pc28.1 ||| ((pc29.1 ||| ((pc30.1 ||| ((pc31.1 ||| (0 <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328))=w} := ⟨_,by conv => lhs; whnf⟩

set_option maxRecDepth 32768 in
private def primeSlab1 : {w : ℕ // (pc32.1 ||| ((pc33.1 ||| ((pc34.1 ||| ((pc35.1 ||| ((pc36.1 ||| ((pc37.1 ||| ((pc38.1 ||| ((pc39.1 ||| ((pc40.1 ||| ((pc41.1 ||| ((pc42.1 ||| ((pc43.1 ||| ((pc44.1 ||| ((pc45.1 ||| ((pc46.1 ||| ((pc47.1 ||| ((pc48.1 ||| ((pc49.1 ||| ((pc50.1 ||| ((pc51.1 ||| ((pc52.1 ||| ((pc53.1 ||| ((pc54.1 ||| ((pc55.1 ||| ((pc56.1 ||| ((pc57.1 ||| ((pc58.1 ||| ((pc59.1 ||| ((pc60.1 ||| ((pc61.1 ||| ((pc62.1 ||| ((pc63.1 ||| (0 <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328))=w} := ⟨_,by conv => lhs; whnf⟩

set_option maxRecDepth 32768 in
private def primeSlab2 : {w : ℕ // (pc64.1 ||| ((pc65.1 ||| ((pc66.1 ||| ((pc67.1 ||| ((pc68.1 ||| ((pc69.1 ||| ((pc70.1 ||| ((pc71.1 ||| ((pc72.1 ||| ((pc73.1 ||| ((pc74.1 ||| ((pc75.1 ||| ((pc76.1 ||| ((pc77.1 ||| ((pc78.1 ||| ((pc79.1 ||| ((pc80.1 ||| ((pc81.1 ||| ((pc82.1 ||| ((pc83.1 ||| ((pc84.1 ||| (0 <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328)) <<< 3328))=w} := ⟨_,by conv => lhs; whnf⟩

private def primeSlab (i : ℕ) :=
  if i<1 then primeSlab0.1 else if i<2 then primeSlab1.1 else if i<3 then primeSlab2.1 else 0

/- Read the same 13-bit odd-prime rank from a checked group of at most 32 original pages. -/
private def pagewisePi (n : ℕ) :=
  if n<3 then n/2 else
    let k := (n-1)/2
    (primePage (k/256) >>> (13*(k%256))) &&& 8191

def smallPi (n : ℕ) :=
  if n<3 then n/2 else
    let k := (n-1)/2
    (primeSlab (k/8192) >>> (13*(k%8192))) &&& 8191

private theorem rankWindow (w c j : ℕ) (hj : j<256) :
    (((w >>> (3328*c)) % 2^3328) >>> (13*j)) % 2^13 =
    (w >>> (3328*c+13*j)) % 2^13 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i<13
  · have inner : 13*j+i<3328 := by omega
    simp [hi,inner,Nat.add_assoc]
  · simp [hi]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private def checkedPrimePages : PLift (∀ i : Fin 85,
    (primeSlab (i.val/32) >>> (3328*(i.val%32))) % 2^3328 = primePage i.val) :=
  ⟨by decide +kernel⟩

theorem smallPi_eq_pagewise (n : ℕ) (hn : n≤43399) : smallPi n = pagewisePi n := by
  by_cases small : n<3
  · simp [smallPi,pagewisePi,small]
  let k := (n-1)/2
  let q := k/256
  let j := k%256
  have bound : q<85 := by dsimp [q,k]; omega
  have pos : j<256 := Nat.mod_lt _ (by decide)
  have outer : k/8192=q/32 := by dsimp [q]; omega
  have inner : 13*(k%8192)=3328*(q%32)+13*j := by dsimp [q,j]; omega
  have page := checkedPrimePages.down ⟨q,bound⟩
  change (primeSlab (q/32) >>> (3328*(q%32))) % 2^3328 = primePage q at page
  simp only [smallPi,pagewisePi,if_neg small]
  change ((primeSlab (k/8192) >>> (13*(k%8192))) &&& 8191) =
    ((primePage q >>> (13*j)) &&& 8191)
  rw [outer,inner,←page,show 8191=2^13-1 by decide]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  exact (rankWindow _ _ _ pos).symm

structure Entry where
  p : ℕ
  pat : ℕ
  mod : ℕ
  top : ℕ
  low : ℕ
  lowRank : ℤ
  neg : ℕ
  base : ℕ

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
def rank (p neg base n : ℕ) : ℤ :=
  if p≤199 then (smallPi n : ℤ)-negRank neg base n else (smallPi n : ℤ)

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
def make (p pat : ℕ) : Entry :=
  let low := max p (43399/p)
  let neg := negative p
  let base := bases p
  ⟨p,pat,(1 <<< p)-1,min 43399 (81744924555066/p^3),low,rank p neg base low,neg,base⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat19 : {w : ℕ // rawPattern 19=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat23 : {w : ℕ // rawPattern 23=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat29 : {w : ℕ // rawPattern 29=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat31 : {w : ℕ // rawPattern 31=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat37 : {w : ℕ // rawPattern 37=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat41 : {w : ℕ // rawPattern 41=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat43 : {w : ℕ // rawPattern 43=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat47 : {w : ℕ // rawPattern 47=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat53 : {w : ℕ // rawPattern 53=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat59 : {w : ℕ // rawPattern 59=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat61 : {w : ℕ // rawPattern 61=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat67 : {w : ℕ // rawPattern 67=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat71 : {w : ℕ // rawPattern 71=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat73 : {w : ℕ // rawPattern 73=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat79 : {w : ℕ // rawPattern 79=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat83 : {w : ℕ // rawPattern 83=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat89 : {w : ℕ // rawPattern 89=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat97 : {w : ℕ // rawPattern 97=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat101 : {w : ℕ // rawPattern 101=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat103 : {w : ℕ // rawPattern 103=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat107 : {w : ℕ // rawPattern 107=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat109 : {w : ℕ // rawPattern 109=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat113 : {w : ℕ // rawPattern 113=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat127 : {w : ℕ // rawPattern 127=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat131 : {w : ℕ // rawPattern 131=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat137 : {w : ℕ // rawPattern 137=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat139 : {w : ℕ // rawPattern 139=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat149 : {w : ℕ // rawPattern 149=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat151 : {w : ℕ // rawPattern 151=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat157 : {w : ℕ // rawPattern 157=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat163 : {w : ℕ // rawPattern 163=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat167 : {w : ℕ // rawPattern 167=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat173 : {w : ℕ // rawPattern 173=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat179 : {w : ℕ // rawPattern 179=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat181 : {w : ℕ // rawPattern 181=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat191 : {w : ℕ // rawPattern 191=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat193 : {w : ℕ // rawPattern 193=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat197 : {w : ℕ // rawPattern 197=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat199 : {w : ℕ // rawPattern 199=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat211 : {w : ℕ // rawPattern 211=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat223 : {w : ℕ // rawPattern 223=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat227 : {w : ℕ // rawPattern 227=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat229 : {w : ℕ // rawPattern 229=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat233 : {w : ℕ // rawPattern 233=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat239 : {w : ℕ // rawPattern 239=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat241 : {w : ℕ // rawPattern 241=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat251 : {w : ℕ // rawPattern 251=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat257 : {w : ℕ // rawPattern 257=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat263 : {w : ℕ // rawPattern 263=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat269 : {w : ℕ // rawPattern 269=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat271 : {w : ℕ // rawPattern 271=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat277 : {w : ℕ // rawPattern 277=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat281 : {w : ℕ // rawPattern 281=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat283 : {w : ℕ // rawPattern 283=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat293 : {w : ℕ // rawPattern 293=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat307 : {w : ℕ // rawPattern 307=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat311 : {w : ℕ // rawPattern 311=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat313 : {w : ℕ // rawPattern 313=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat317 : {w : ℕ // rawPattern 317=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat331 : {w : ℕ // rawPattern 331=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat337 : {w : ℕ // rawPattern 337=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat347 : {w : ℕ // rawPattern 347=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat349 : {w : ℕ // rawPattern 349=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat353 : {w : ℕ // rawPattern 353=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat359 : {w : ℕ // rawPattern 359=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat367 : {w : ℕ // rawPattern 367=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat373 : {w : ℕ // rawPattern 373=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat379 : {w : ℕ // rawPattern 379=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat383 : {w : ℕ // rawPattern 383=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat389 : {w : ℕ // rawPattern 389=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat397 : {w : ℕ // rawPattern 397=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat401 : {w : ℕ // rawPattern 401=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat409 : {w : ℕ // rawPattern 409=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat419 : {w : ℕ // rawPattern 419=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat421 : {w : ℕ // rawPattern 421=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat431 : {w : ℕ // rawPattern 431=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat433 : {w : ℕ // rawPattern 433=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat439 : {w : ℕ // rawPattern 439=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat443 : {w : ℕ // rawPattern 443=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat449 : {w : ℕ // rawPattern 449=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat457 : {w : ℕ // rawPattern 457=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat461 : {w : ℕ // rawPattern 461=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat463 : {w : ℕ // rawPattern 463=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat467 : {w : ℕ // rawPattern 467=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat479 : {w : ℕ // rawPattern 479=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat487 : {w : ℕ // rawPattern 487=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat491 : {w : ℕ // rawPattern 491=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat499 : {w : ℕ // rawPattern 499=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat503 : {w : ℕ // rawPattern 503=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat509 : {w : ℕ // rawPattern 509=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat521 : {w : ℕ // rawPattern 521=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat523 : {w : ℕ // rawPattern 523=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat541 : {w : ℕ // rawPattern 541=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat547 : {w : ℕ // rawPattern 547=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat557 : {w : ℕ // rawPattern 557=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat563 : {w : ℕ // rawPattern 563=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat569 : {w : ℕ // rawPattern 569=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat571 : {w : ℕ // rawPattern 571=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat577 : {w : ℕ // rawPattern 577=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat587 : {w : ℕ // rawPattern 587=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat593 : {w : ℕ // rawPattern 593=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat599 : {w : ℕ // rawPattern 599=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat601 : {w : ℕ // rawPattern 601=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat607 : {w : ℕ // rawPattern 607=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat613 : {w : ℕ // rawPattern 613=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat617 : {w : ℕ // rawPattern 617=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat619 : {w : ℕ // rawPattern 619=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat631 : {w : ℕ // rawPattern 631=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat641 : {w : ℕ // rawPattern 641=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat643 : {w : ℕ // rawPattern 643=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat647 : {w : ℕ // rawPattern 647=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat653 : {w : ℕ // rawPattern 653=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat659 : {w : ℕ // rawPattern 659=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat661 : {w : ℕ // rawPattern 661=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat673 : {w : ℕ // rawPattern 673=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat677 : {w : ℕ // rawPattern 677=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat683 : {w : ℕ // rawPattern 683=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat691 : {w : ℕ // rawPattern 691=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat701 : {w : ℕ // rawPattern 701=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat709 : {w : ℕ // rawPattern 709=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat719 : {w : ℕ // rawPattern 719=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat727 : {w : ℕ // rawPattern 727=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat733 : {w : ℕ // rawPattern 733=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat739 : {w : ℕ // rawPattern 739=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat743 : {w : ℕ // rawPattern 743=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat751 : {w : ℕ // rawPattern 751=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat757 : {w : ℕ // rawPattern 757=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat761 : {w : ℕ // rawPattern 761=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat769 : {w : ℕ // rawPattern 769=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat773 : {w : ℕ // rawPattern 773=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat787 : {w : ℕ // rawPattern 787=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat797 : {w : ℕ // rawPattern 797=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat809 : {w : ℕ // rawPattern 809=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat811 : {w : ℕ // rawPattern 811=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat821 : {w : ℕ // rawPattern 821=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat823 : {w : ℕ // rawPattern 823=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat827 : {w : ℕ // rawPattern 827=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat829 : {w : ℕ // rawPattern 829=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat839 : {w : ℕ // rawPattern 839=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat853 : {w : ℕ // rawPattern 853=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat857 : {w : ℕ // rawPattern 857=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat859 : {w : ℕ // rawPattern 859=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat863 : {w : ℕ // rawPattern 863=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat877 : {w : ℕ // rawPattern 877=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat881 : {w : ℕ // rawPattern 881=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat883 : {w : ℕ // rawPattern 883=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat887 : {w : ℕ // rawPattern 887=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat907 : {w : ℕ // rawPattern 907=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat911 : {w : ℕ // rawPattern 911=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat919 : {w : ℕ // rawPattern 919=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat929 : {w : ℕ // rawPattern 929=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat937 : {w : ℕ // rawPattern 937=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat941 : {w : ℕ // rawPattern 941=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat947 : {w : ℕ // rawPattern 947=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat953 : {w : ℕ // rawPattern 953=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat967 : {w : ℕ // rawPattern 967=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat971 : {w : ℕ // rawPattern 971=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat977 : {w : ℕ // rawPattern 977=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat983 : {w : ℕ // rawPattern 983=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat991 : {w : ℕ // rawPattern 991=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat997 : {w : ℕ // rawPattern 997=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1009 : {w : ℕ // rawPattern 1009=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1013 : {w : ℕ // rawPattern 1013=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1019 : {w : ℕ // rawPattern 1019=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1021 : {w : ℕ // rawPattern 1021=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1031 : {w : ℕ // rawPattern 1031=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1033 : {w : ℕ // rawPattern 1033=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1039 : {w : ℕ // rawPattern 1039=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1049 : {w : ℕ // rawPattern 1049=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1051 : {w : ℕ // rawPattern 1051=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1061 : {w : ℕ // rawPattern 1061=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1063 : {w : ℕ // rawPattern 1063=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1069 : {w : ℕ // rawPattern 1069=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1087 : {w : ℕ // rawPattern 1087=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1091 : {w : ℕ // rawPattern 1091=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1093 : {w : ℕ // rawPattern 1093=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1097 : {w : ℕ // rawPattern 1097=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1103 : {w : ℕ // rawPattern 1103=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1109 : {w : ℕ // rawPattern 1109=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1117 : {w : ℕ // rawPattern 1117=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1123 : {w : ℕ // rawPattern 1123=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1129 : {w : ℕ // rawPattern 1129=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1151 : {w : ℕ // rawPattern 1151=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1153 : {w : ℕ // rawPattern 1153=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1163 : {w : ℕ // rawPattern 1163=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1171 : {w : ℕ // rawPattern 1171=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1181 : {w : ℕ // rawPattern 1181=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1187 : {w : ℕ // rawPattern 1187=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1193 : {w : ℕ // rawPattern 1193=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1201 : {w : ℕ // rawPattern 1201=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1213 : {w : ℕ // rawPattern 1213=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1217 : {w : ℕ // rawPattern 1217=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1223 : {w : ℕ // rawPattern 1223=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1229 : {w : ℕ // rawPattern 1229=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1231 : {w : ℕ // rawPattern 1231=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1237 : {w : ℕ // rawPattern 1237=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1249 : {w : ℕ // rawPattern 1249=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1259 : {w : ℕ // rawPattern 1259=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1277 : {w : ℕ // rawPattern 1277=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1279 : {w : ℕ // rawPattern 1279=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1283 : {w : ℕ // rawPattern 1283=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1289 : {w : ℕ // rawPattern 1289=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1291 : {w : ℕ // rawPattern 1291=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1297 : {w : ℕ // rawPattern 1297=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1301 : {w : ℕ // rawPattern 1301=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1303 : {w : ℕ // rawPattern 1303=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1307 : {w : ℕ // rawPattern 1307=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1319 : {w : ℕ // rawPattern 1319=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1321 : {w : ℕ // rawPattern 1321=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1327 : {w : ℕ // rawPattern 1327=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1361 : {w : ℕ // rawPattern 1361=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1367 : {w : ℕ // rawPattern 1367=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1373 : {w : ℕ // rawPattern 1373=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1381 : {w : ℕ // rawPattern 1381=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1399 : {w : ℕ // rawPattern 1399=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1409 : {w : ℕ // rawPattern 1409=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1423 : {w : ℕ // rawPattern 1423=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1427 : {w : ℕ // rawPattern 1427=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1429 : {w : ℕ // rawPattern 1429=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1433 : {w : ℕ // rawPattern 1433=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1439 : {w : ℕ // rawPattern 1439=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1447 : {w : ℕ // rawPattern 1447=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1451 : {w : ℕ // rawPattern 1451=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1453 : {w : ℕ // rawPattern 1453=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1459 : {w : ℕ // rawPattern 1459=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1471 : {w : ℕ // rawPattern 1471=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1481 : {w : ℕ // rawPattern 1481=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1483 : {w : ℕ // rawPattern 1483=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1487 : {w : ℕ // rawPattern 1487=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1489 : {w : ℕ // rawPattern 1489=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1493 : {w : ℕ // rawPattern 1493=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1499 : {w : ℕ // rawPattern 1499=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1511 : {w : ℕ // rawPattern 1511=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1523 : {w : ℕ // rawPattern 1523=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1531 : {w : ℕ // rawPattern 1531=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1543 : {w : ℕ // rawPattern 1543=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1549 : {w : ℕ // rawPattern 1549=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1553 : {w : ℕ // rawPattern 1553=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1559 : {w : ℕ // rawPattern 1559=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1567 : {w : ℕ // rawPattern 1567=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1571 : {w : ℕ // rawPattern 1571=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1579 : {w : ℕ // rawPattern 1579=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1583 : {w : ℕ // rawPattern 1583=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1597 : {w : ℕ // rawPattern 1597=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1601 : {w : ℕ // rawPattern 1601=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1607 : {w : ℕ // rawPattern 1607=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1609 : {w : ℕ // rawPattern 1609=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1613 : {w : ℕ // rawPattern 1613=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1619 : {w : ℕ // rawPattern 1619=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1621 : {w : ℕ // rawPattern 1621=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1627 : {w : ℕ // rawPattern 1627=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1637 : {w : ℕ // rawPattern 1637=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1657 : {w : ℕ // rawPattern 1657=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1663 : {w : ℕ // rawPattern 1663=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1667 : {w : ℕ // rawPattern 1667=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1669 : {w : ℕ // rawPattern 1669=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1693 : {w : ℕ // rawPattern 1693=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1697 : {w : ℕ // rawPattern 1697=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1699 : {w : ℕ // rawPattern 1699=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1709 : {w : ℕ // rawPattern 1709=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1721 : {w : ℕ // rawPattern 1721=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1723 : {w : ℕ // rawPattern 1723=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1733 : {w : ℕ // rawPattern 1733=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1741 : {w : ℕ // rawPattern 1741=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1747 : {w : ℕ // rawPattern 1747=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1753 : {w : ℕ // rawPattern 1753=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1759 : {w : ℕ // rawPattern 1759=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1777 : {w : ℕ // rawPattern 1777=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1783 : {w : ℕ // rawPattern 1783=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1787 : {w : ℕ // rawPattern 1787=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1789 : {w : ℕ // rawPattern 1789=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1801 : {w : ℕ // rawPattern 1801=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1811 : {w : ℕ // rawPattern 1811=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1823 : {w : ℕ // rawPattern 1823=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1831 : {w : ℕ // rawPattern 1831=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1847 : {w : ℕ // rawPattern 1847=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1861 : {w : ℕ // rawPattern 1861=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1867 : {w : ℕ // rawPattern 1867=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1871 : {w : ℕ // rawPattern 1871=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1873 : {w : ℕ // rawPattern 1873=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1877 : {w : ℕ // rawPattern 1877=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1879 : {w : ℕ // rawPattern 1879=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1889 : {w : ℕ // rawPattern 1889=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1901 : {w : ℕ // rawPattern 1901=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1907 : {w : ℕ // rawPattern 1907=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1913 : {w : ℕ // rawPattern 1913=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1931 : {w : ℕ // rawPattern 1931=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1933 : {w : ℕ // rawPattern 1933=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1949 : {w : ℕ // rawPattern 1949=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1951 : {w : ℕ // rawPattern 1951=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1973 : {w : ℕ // rawPattern 1973=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1979 : {w : ℕ // rawPattern 1979=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1987 : {w : ℕ // rawPattern 1987=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1993 : {w : ℕ // rawPattern 1993=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1997 : {w : ℕ // rawPattern 1997=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat1999 : {w : ℕ // rawPattern 1999=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2003 : {w : ℕ // rawPattern 2003=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2011 : {w : ℕ // rawPattern 2011=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2017 : {w : ℕ // rawPattern 2017=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2027 : {w : ℕ // rawPattern 2027=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2029 : {w : ℕ // rawPattern 2029=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2039 : {w : ℕ // rawPattern 2039=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2053 : {w : ℕ // rawPattern 2053=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2063 : {w : ℕ // rawPattern 2063=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2069 : {w : ℕ // rawPattern 2069=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2081 : {w : ℕ // rawPattern 2081=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2083 : {w : ℕ // rawPattern 2083=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2087 : {w : ℕ // rawPattern 2087=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2089 : {w : ℕ // rawPattern 2089=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2099 : {w : ℕ // rawPattern 2099=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2111 : {w : ℕ // rawPattern 2111=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2113 : {w : ℕ // rawPattern 2113=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2129 : {w : ℕ // rawPattern 2129=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2131 : {w : ℕ // rawPattern 2131=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2137 : {w : ℕ // rawPattern 2137=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2141 : {w : ℕ // rawPattern 2141=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2143 : {w : ℕ // rawPattern 2143=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2153 : {w : ℕ // rawPattern 2153=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2161 : {w : ℕ // rawPattern 2161=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2179 : {w : ℕ // rawPattern 2179=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2203 : {w : ℕ // rawPattern 2203=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2207 : {w : ℕ // rawPattern 2207=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2213 : {w : ℕ // rawPattern 2213=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2221 : {w : ℕ // rawPattern 2221=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2237 : {w : ℕ // rawPattern 2237=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2239 : {w : ℕ // rawPattern 2239=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2243 : {w : ℕ // rawPattern 2243=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2251 : {w : ℕ // rawPattern 2251=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2267 : {w : ℕ // rawPattern 2267=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2269 : {w : ℕ // rawPattern 2269=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2273 : {w : ℕ // rawPattern 2273=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2281 : {w : ℕ // rawPattern 2281=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2287 : {w : ℕ // rawPattern 2287=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2293 : {w : ℕ // rawPattern 2293=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2297 : {w : ℕ // rawPattern 2297=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2309 : {w : ℕ // rawPattern 2309=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2311 : {w : ℕ // rawPattern 2311=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2333 : {w : ℕ // rawPattern 2333=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2339 : {w : ℕ // rawPattern 2339=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2341 : {w : ℕ // rawPattern 2341=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2347 : {w : ℕ // rawPattern 2347=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2351 : {w : ℕ // rawPattern 2351=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2357 : {w : ℕ // rawPattern 2357=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2371 : {w : ℕ // rawPattern 2371=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2377 : {w : ℕ // rawPattern 2377=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2381 : {w : ℕ // rawPattern 2381=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2383 : {w : ℕ // rawPattern 2383=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2389 : {w : ℕ // rawPattern 2389=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2393 : {w : ℕ // rawPattern 2393=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2399 : {w : ℕ // rawPattern 2399=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2411 : {w : ℕ // rawPattern 2411=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2417 : {w : ℕ // rawPattern 2417=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2423 : {w : ℕ // rawPattern 2423=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2437 : {w : ℕ // rawPattern 2437=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2441 : {w : ℕ // rawPattern 2441=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2447 : {w : ℕ // rawPattern 2447=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2459 : {w : ℕ // rawPattern 2459=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2467 : {w : ℕ // rawPattern 2467=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2473 : {w : ℕ // rawPattern 2473=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2477 : {w : ℕ // rawPattern 2477=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2503 : {w : ℕ // rawPattern 2503=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2521 : {w : ℕ // rawPattern 2521=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2531 : {w : ℕ // rawPattern 2531=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2539 : {w : ℕ // rawPattern 2539=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2543 : {w : ℕ // rawPattern 2543=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2549 : {w : ℕ // rawPattern 2549=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2551 : {w : ℕ // rawPattern 2551=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2557 : {w : ℕ // rawPattern 2557=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2579 : {w : ℕ // rawPattern 2579=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2591 : {w : ℕ // rawPattern 2591=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2593 : {w : ℕ // rawPattern 2593=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2609 : {w : ℕ // rawPattern 2609=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2617 : {w : ℕ // rawPattern 2617=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2621 : {w : ℕ // rawPattern 2621=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2633 : {w : ℕ // rawPattern 2633=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2647 : {w : ℕ // rawPattern 2647=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2657 : {w : ℕ // rawPattern 2657=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2659 : {w : ℕ // rawPattern 2659=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2663 : {w : ℕ // rawPattern 2663=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2671 : {w : ℕ // rawPattern 2671=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2677 : {w : ℕ // rawPattern 2677=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2683 : {w : ℕ // rawPattern 2683=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2687 : {w : ℕ // rawPattern 2687=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2689 : {w : ℕ // rawPattern 2689=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2693 : {w : ℕ // rawPattern 2693=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2699 : {w : ℕ // rawPattern 2699=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2707 : {w : ℕ // rawPattern 2707=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2711 : {w : ℕ // rawPattern 2711=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2713 : {w : ℕ // rawPattern 2713=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2719 : {w : ℕ // rawPattern 2719=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2729 : {w : ℕ // rawPattern 2729=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2731 : {w : ℕ // rawPattern 2731=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2741 : {w : ℕ // rawPattern 2741=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2749 : {w : ℕ // rawPattern 2749=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2753 : {w : ℕ // rawPattern 2753=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2767 : {w : ℕ // rawPattern 2767=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2777 : {w : ℕ // rawPattern 2777=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2789 : {w : ℕ // rawPattern 2789=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2791 : {w : ℕ // rawPattern 2791=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2797 : {w : ℕ // rawPattern 2797=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2801 : {w : ℕ // rawPattern 2801=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2803 : {w : ℕ // rawPattern 2803=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2819 : {w : ℕ // rawPattern 2819=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2833 : {w : ℕ // rawPattern 2833=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2837 : {w : ℕ // rawPattern 2837=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2843 : {w : ℕ // rawPattern 2843=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2851 : {w : ℕ // rawPattern 2851=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2857 : {w : ℕ // rawPattern 2857=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2861 : {w : ℕ // rawPattern 2861=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2879 : {w : ℕ // rawPattern 2879=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2887 : {w : ℕ // rawPattern 2887=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2897 : {w : ℕ // rawPattern 2897=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2903 : {w : ℕ // rawPattern 2903=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2909 : {w : ℕ // rawPattern 2909=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2917 : {w : ℕ // rawPattern 2917=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2927 : {w : ℕ // rawPattern 2927=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2939 : {w : ℕ // rawPattern 2939=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2953 : {w : ℕ // rawPattern 2953=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2957 : {w : ℕ // rawPattern 2957=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2963 : {w : ℕ // rawPattern 2963=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2969 : {w : ℕ // rawPattern 2969=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2971 : {w : ℕ // rawPattern 2971=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat2999 : {w : ℕ // rawPattern 2999=w} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
private def pat3001 : {w : ℕ // rawPattern 3001=w} := ⟨_,by conv => lhs; whnf⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
def roster : List Entry := [
  make 19 pat19.1,make 23 pat23.1,make 29 pat29.1,make 31 pat31.1,make 37 pat37.1,make 41 pat41.1,
  make 43 pat43.1,make 47 pat47.1,make 53 pat53.1,make 59 pat59.1,make 61 pat61.1,make 67 pat67.1,
  make 71 pat71.1,make 73 pat73.1,make 79 pat79.1,make 83 pat83.1,make 89 pat89.1,make 97 pat97.1,
  make 101 pat101.1,make 103 pat103.1,make 107 pat107.1,make 109 pat109.1,make 113 pat113.1,make 127 pat127.1,
  make 131 pat131.1,make 137 pat137.1,make 139 pat139.1,make 149 pat149.1,make 151 pat151.1,make 157 pat157.1,
  make 163 pat163.1,make 167 pat167.1,make 173 pat173.1,make 179 pat179.1,make 181 pat181.1,make 191 pat191.1,
  make 193 pat193.1,make 197 pat197.1,make 199 pat199.1,make 211 pat211.1,make 223 pat223.1,make 227 pat227.1,
  make 229 pat229.1,make 233 pat233.1,make 239 pat239.1,make 241 pat241.1,make 251 pat251.1,make 257 pat257.1,
  make 263 pat263.1,make 269 pat269.1,make 271 pat271.1,make 277 pat277.1,make 281 pat281.1,make 283 pat283.1,
  make 293 pat293.1,make 307 pat307.1,make 311 pat311.1,make 313 pat313.1,make 317 pat317.1,make 331 pat331.1,
  make 337 pat337.1,make 347 pat347.1,make 349 pat349.1,make 353 pat353.1,make 359 pat359.1,make 367 pat367.1,
  make 373 pat373.1,make 379 pat379.1,make 383 pat383.1,make 389 pat389.1,make 397 pat397.1,make 401 pat401.1,
  make 409 pat409.1,make 419 pat419.1,make 421 pat421.1,make 431 pat431.1,make 433 pat433.1,make 439 pat439.1,
  make 443 pat443.1,make 449 pat449.1,make 457 pat457.1,make 461 pat461.1,make 463 pat463.1,make 467 pat467.1,
  make 479 pat479.1,make 487 pat487.1,make 491 pat491.1,make 499 pat499.1,make 503 pat503.1,make 509 pat509.1,
  make 521 pat521.1,make 523 pat523.1,make 541 pat541.1,make 547 pat547.1,make 557 pat557.1,make 563 pat563.1,
  make 569 pat569.1,make 571 pat571.1,make 577 pat577.1,make 587 pat587.1,make 593 pat593.1,make 599 pat599.1,
  make 601 pat601.1,make 607 pat607.1,make 613 pat613.1,make 617 pat617.1,make 619 pat619.1,make 631 pat631.1,
  make 641 pat641.1,make 643 pat643.1,make 647 pat647.1,make 653 pat653.1,make 659 pat659.1,make 661 pat661.1,
  make 673 pat673.1,make 677 pat677.1,make 683 pat683.1,make 691 pat691.1,make 701 pat701.1,make 709 pat709.1,
  make 719 pat719.1,make 727 pat727.1,make 733 pat733.1,make 739 pat739.1,make 743 pat743.1,make 751 pat751.1,
  make 757 pat757.1,make 761 pat761.1,make 769 pat769.1,make 773 pat773.1,make 787 pat787.1,make 797 pat797.1,
  make 809 pat809.1,make 811 pat811.1,make 821 pat821.1,make 823 pat823.1,make 827 pat827.1,make 829 pat829.1,
  make 839 pat839.1,make 853 pat853.1,make 857 pat857.1,make 859 pat859.1,make 863 pat863.1,make 877 pat877.1,
  make 881 pat881.1,make 883 pat883.1,make 887 pat887.1,make 907 pat907.1,make 911 pat911.1,make 919 pat919.1,
  make 929 pat929.1,make 937 pat937.1,make 941 pat941.1,make 947 pat947.1,make 953 pat953.1,make 967 pat967.1,
  make 971 pat971.1,make 977 pat977.1,make 983 pat983.1,make 991 pat991.1,make 997 pat997.1,make 1009 pat1009.1,
  make 1013 pat1013.1,make 1019 pat1019.1,make 1021 pat1021.1,make 1031 pat1031.1,make 1033 pat1033.1,make 1039 pat1039.1,
  make 1049 pat1049.1,make 1051 pat1051.1,make 1061 pat1061.1,make 1063 pat1063.1,make 1069 pat1069.1,make 1087 pat1087.1,
  make 1091 pat1091.1,make 1093 pat1093.1,make 1097 pat1097.1,make 1103 pat1103.1,make 1109 pat1109.1,make 1117 pat1117.1,
  make 1123 pat1123.1,make 1129 pat1129.1,make 1151 pat1151.1,make 1153 pat1153.1,make 1163 pat1163.1,make 1171 pat1171.1,
  make 1181 pat1181.1,make 1187 pat1187.1,make 1193 pat1193.1,make 1201 pat1201.1,make 1213 pat1213.1,make 1217 pat1217.1,
  make 1223 pat1223.1,make 1229 pat1229.1,make 1231 pat1231.1,make 1237 pat1237.1,make 1249 pat1249.1,make 1259 pat1259.1,
  make 1277 pat1277.1,make 1279 pat1279.1,make 1283 pat1283.1,make 1289 pat1289.1,make 1291 pat1291.1,make 1297 pat1297.1,
  make 1301 pat1301.1,make 1303 pat1303.1,make 1307 pat1307.1,make 1319 pat1319.1,make 1321 pat1321.1,make 1327 pat1327.1,
  make 1361 pat1361.1,make 1367 pat1367.1,make 1373 pat1373.1,make 1381 pat1381.1,make 1399 pat1399.1,make 1409 pat1409.1,
  make 1423 pat1423.1,make 1427 pat1427.1,make 1429 pat1429.1,make 1433 pat1433.1,make 1439 pat1439.1,make 1447 pat1447.1,
  make 1451 pat1451.1,make 1453 pat1453.1,make 1459 pat1459.1,make 1471 pat1471.1,make 1481 pat1481.1,make 1483 pat1483.1,
  make 1487 pat1487.1,make 1489 pat1489.1,make 1493 pat1493.1,make 1499 pat1499.1,make 1511 pat1511.1,make 1523 pat1523.1,
  make 1531 pat1531.1,make 1543 pat1543.1,make 1549 pat1549.1,make 1553 pat1553.1,make 1559 pat1559.1,make 1567 pat1567.1,
  make 1571 pat1571.1,make 1579 pat1579.1,make 1583 pat1583.1,make 1597 pat1597.1,make 1601 pat1601.1,make 1607 pat1607.1,
  make 1609 pat1609.1,make 1613 pat1613.1,make 1619 pat1619.1,make 1621 pat1621.1,make 1627 pat1627.1,make 1637 pat1637.1,
  make 1657 pat1657.1,make 1663 pat1663.1,make 1667 pat1667.1,make 1669 pat1669.1,make 1693 pat1693.1,make 1697 pat1697.1,
  make 1699 pat1699.1,make 1709 pat1709.1,make 1721 pat1721.1,make 1723 pat1723.1,make 1733 pat1733.1,make 1741 pat1741.1,
  make 1747 pat1747.1,make 1753 pat1753.1,make 1759 pat1759.1,make 1777 pat1777.1,make 1783 pat1783.1,make 1787 pat1787.1,
  make 1789 pat1789.1,make 1801 pat1801.1,make 1811 pat1811.1,make 1823 pat1823.1,make 1831 pat1831.1,make 1847 pat1847.1,
  make 1861 pat1861.1,make 1867 pat1867.1,make 1871 pat1871.1,make 1873 pat1873.1,make 1877 pat1877.1,make 1879 pat1879.1,
  make 1889 pat1889.1,make 1901 pat1901.1,make 1907 pat1907.1,make 1913 pat1913.1,make 1931 pat1931.1,make 1933 pat1933.1,
  make 1949 pat1949.1,make 1951 pat1951.1,make 1973 pat1973.1,make 1979 pat1979.1,make 1987 pat1987.1,make 1993 pat1993.1,
  make 1997 pat1997.1,make 1999 pat1999.1,make 2003 pat2003.1,make 2011 pat2011.1,make 2017 pat2017.1,make 2027 pat2027.1,
  make 2029 pat2029.1,make 2039 pat2039.1,make 2053 pat2053.1,make 2063 pat2063.1,make 2069 pat2069.1,make 2081 pat2081.1,
  make 2083 pat2083.1,make 2087 pat2087.1,make 2089 pat2089.1,make 2099 pat2099.1,make 2111 pat2111.1,make 2113 pat2113.1,
  make 2129 pat2129.1,make 2131 pat2131.1,make 2137 pat2137.1,make 2141 pat2141.1,make 2143 pat2143.1,make 2153 pat2153.1,
  make 2161 pat2161.1,make 2179 pat2179.1,make 2203 pat2203.1,make 2207 pat2207.1,make 2213 pat2213.1,make 2221 pat2221.1,
  make 2237 pat2237.1,make 2239 pat2239.1,make 2243 pat2243.1,make 2251 pat2251.1,make 2267 pat2267.1,make 2269 pat2269.1,
  make 2273 pat2273.1,make 2281 pat2281.1,make 2287 pat2287.1,make 2293 pat2293.1,make 2297 pat2297.1,make 2309 pat2309.1,
  make 2311 pat2311.1,make 2333 pat2333.1,make 2339 pat2339.1,make 2341 pat2341.1,make 2347 pat2347.1,make 2351 pat2351.1,
  make 2357 pat2357.1,make 2371 pat2371.1,make 2377 pat2377.1,make 2381 pat2381.1,make 2383 pat2383.1,make 2389 pat2389.1,
  make 2393 pat2393.1,make 2399 pat2399.1,make 2411 pat2411.1,make 2417 pat2417.1,make 2423 pat2423.1,make 2437 pat2437.1,
  make 2441 pat2441.1,make 2447 pat2447.1,make 2459 pat2459.1,make 2467 pat2467.1,make 2473 pat2473.1,make 2477 pat2477.1,
  make 2503 pat2503.1,make 2521 pat2521.1,make 2531 pat2531.1,make 2539 pat2539.1,make 2543 pat2543.1,make 2549 pat2549.1,
  make 2551 pat2551.1,make 2557 pat2557.1,make 2579 pat2579.1,make 2591 pat2591.1,make 2593 pat2593.1,make 2609 pat2609.1,
  make 2617 pat2617.1,make 2621 pat2621.1,make 2633 pat2633.1,make 2647 pat2647.1,make 2657 pat2657.1,make 2659 pat2659.1,
  make 2663 pat2663.1,make 2671 pat2671.1,make 2677 pat2677.1,make 2683 pat2683.1,make 2687 pat2687.1,make 2689 pat2689.1,
  make 2693 pat2693.1,make 2699 pat2699.1,make 2707 pat2707.1,make 2711 pat2711.1,make 2713 pat2713.1,make 2719 pat2719.1,
  make 2729 pat2729.1,make 2731 pat2731.1,make 2741 pat2741.1,make 2749 pat2749.1,make 2753 pat2753.1,make 2767 pat2767.1,
  make 2777 pat2777.1,make 2789 pat2789.1,make 2791 pat2791.1,make 2797 pat2797.1,make 2801 pat2801.1,make 2803 pat2803.1,
  make 2819 pat2819.1,make 2833 pat2833.1,make 2837 pat2837.1,make 2843 pat2843.1,make 2851 pat2851.1,make 2857 pat2857.1,
  make 2861 pat2861.1,make 2879 pat2879.1,make 2887 pat2887.1,make 2897 pat2897.1,make 2903 pat2903.1,make 2909 pat2909.1,
  make 2917 pat2917.1,make 2927 pat2927.1,make 2939 pat2939.1,make 2953 pat2953.1,make 2957 pat2957.1,make 2963 pat2963.1,
  make 2969 pat2969.1,make 2971 pat2971.1,make 2999 pat2999.1,make 3001 pat3001.1
  ]
end Astra247824.FullLookup


/- A single signed, weighted sieve scan across all active primes of a complete segment. -/
namespace Astra247824.FullLookup

set_option maxRecDepth 131072 in
def coeff (e : Entry) (capacity : ℕ) : ℤ :=
  if e.p≤23 then 0 else
    let u := min e.top (capacity/e.p)
    if u≤e.low then 0 else rank e.p e.neg e.base u - e.lowRank

set_option maxRecDepth 131072 in
def accumulate (lo capacity word alive : ℕ) (sum : ℤ) : List Entry → ℤ
  | [] => sum
  | e::es =>
    if capacity<e.p*e.p then sum else
      let total := sum + (alive : ℤ)*coeff e capacity
      let next := stageUpdate word alive e.pat e.mod e.p lo
      accumulate lo capacity next.1 next.2 total es

set_option maxRecDepth 131072 in
def basePrimes : List ℕ := [17,13,11,7,5,3,2]

set_option maxRecDepth 131072 in
def row (b : ℕ) : ℤ :=
  let lo := b*65536
  let word := blockMask lo 65536 basePrimes
  let alive := smallRank 7 (lo+65535) - smallRank 7 (lo-1)
  accumulate lo (81744924555066/((b+1)*65536)) word alive 0 roster

set_option maxRecDepth 131072 in
def interval : ℕ → ℕ → ℤ
  | 0, i => row i
  | k+1, i => interval k i + interval k (i+(1 <<< k))
end Astra247824.FullLookup

namespace Astra247824.FullLookup
open Finset
def offset (base q : ℕ) := (base >>> (12*q)) &&& 4095

def wordPiece (word a k : ℕ) := (word >>> a) &&& ((1 <<< k)-1)

def smallPrimes := [29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]

theorem small_mem {p : ℕ} (pp : p.Prime) (h : 23<p) (l : p≤199) : p∈smallPrimes := by
  have table : ∀ i : Fin 200, i.val.Prime → (23 < i.val) → (i.val ∈ smallPrimes) := by decide +kernel
  exact table ⟨p,by omega⟩ pp h

def gridTree (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, n => f n
  | k+1, n => gridTree f k n && gridTree f k (n+2^k)

theorem grid_index {f : ℕ → Bool} {k lo : ℕ} (h : gridTree f k lo = true)
    {d : ℕ} (left : lo≤d) (right : d<lo+2^k) : f d=true := by
  induction k generalizing lo with
  | zero => have same : d=lo := by simp at right; omega
            simpa [gridTree,same] using h
  | succ k ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at right
    by_cases small : d<lo+2^k
    · exact ih a left small
    · exact ih b (by omega) (by omega)

theorem grid_pair {f : ℕ → Bool} {k i : ℕ}
    (l : gridTree f k i=true) (r : gridTree f k (i+2^k)=true) : gridTree f (k+1) i=true := by
  simp [gridTree,l,r]
end Astra247824.FullLookup

namespace Astra247824.FullLookup

class CheckedWeights : Prop where
  grid {n : ℕ} (hn : n ≤ 43399) : smallPi n = Nat.primeCounting n ∧
    ((HardTail.denomWords 29).1.testBit n = true ↔ n.Prime)
  word {p : ℕ} (hp : p ∈ smallPrimes) : negative p = (HardTail.denomWords p).2
  zero {p : ℕ} (hp : p ∈ smallPrimes) : offset (bases p) 0 = 0
  next {p q : ℕ} (hp : p ∈ smallPrimes) (hq : q < 678) :
    offset (bases p) (q+1) = offset (bases p) q + GlobalRank.pop64 (wordPiece (negative p) (64*q) 64)

variable [audit : CheckedWeights]
include audit

theorem smallPi_correct {n : ℕ} (h : n ≤ 43399) : smallPi n = Nat.primeCounting n :=
  (CheckedWeights.grid h).1

theorem posBit {p d : ℕ} (h : d ≤ 43399) : (HardTail.denomWords p).1.testBit d = true ↔ d.Prime :=
  (CheckedWeights.grid h).2

theorem negWord {p : ℕ} (h : p ∈ smallPrimes) : negative p = (HardTail.denomWords p).2 :=
  CheckedWeights.word h

theorem zeroOffset {p : ℕ} (h : p ∈ smallPrimes) : offset (bases p) 0 = 0 :=
  CheckedWeights.zero h

theorem nextOffset {p q : ℕ} (hp : p ∈ smallPrimes) (hq : q < 678) :
    offset (bases p) (q+1) = offset (bases p) q + GlobalRank.pop64 (wordPiece (negative p) (64*q) 64) :=
  CheckedWeights.next hp hq

end Astra247824.FullLookup


/- Correctness of the constant-time cumulative denominator rank. -/
namespace Astra247824.FullLookup
open Finset ArithmeticFunction Leaves
variable [audit : CheckedWeights]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
def bitPrefix (w n : ℕ) := ((range n).filter (fun i => w.testBit i)).card

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem prefix_add (w a b : ℕ) : bitPrefix w (a+b) = bitPrefix w a +
    ((range b).filter (fun i => w.testBit (a+i))).card := by
  have eq := sum_range_add (fun i => if w.testBit i then (1 : ℕ) else 0) a b
  simpa only [bitPrefix,sum_boole,Nat.cast_id] using eq

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem piece_count (word a t : ℕ) (h : t≤64) : GlobalRank.pop64 (wordPiece word a t) =
    ((range t).filter (fun i => word.testBit (a+i))).card := by
  have eq : wordPiece word a t=(word >>> a)%2^t := by
    simp only [wordPiece,Nat.shiftLeft_eq,Nat.one_mul,Nat.and_two_pow_sub_one_eq_mod]
  rw [eq,GlobalRank.pop64_spec _ ((Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) h))]
  congr 1
  ext i
  simp only [mem_filter,mem_range,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨_,hi,flag⟩
    exact ⟨hi,by simpa only [Nat.add_comm] using flag⟩
  · rintro ⟨hi,flag⟩
    exact ⟨hi.trans_le h,hi,by simpa only [Nat.add_comm] using flag⟩

include audit in
set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem offset_count {p : ℕ} (hp : p∈smallPrimes) (q : ℕ) (hq : q≤678) :
    offset (bases p) q = bitPrefix (negative p) (64*q) := by
  induction q with
  | zero => simpa [bitPrefix] using zeroOffset hp
  | succ q ih =>
    rw [nextOffset hp (by omega), ih (by omega),Nat.mul_succ,prefix_add,piece_count _ _ _ (by decide)]

include audit in
set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
theorem negRank_correct {p n : ℕ} (hp : p∈smallPrimes) (hn : n≤43399) :
    negRank (negative p) (bases p) n = bitPrefix (HardTail.denomWords p).2 (n+1) := by
  change offset (bases p) (n/64) + GlobalRank.pop64 (wordPiece (negative p) (64*(n/64)) (n%64+1)) = _
  rw [offset_count hp _ (by omega),piece_count (negative p) _ _ (by omega),← prefix_add,negWord hp]
  exact congrArg (bitPrefix (HardTail.denomWords p).2) (by omega)

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem big_no_negative {p : ℕ} (pp : p.Prime) (large : 199<p) :
    (HardTail.denomWords p).2=0 := by
  by_cases h : 256≤p
  · simp [HardTail.denomWords,h]
  · have all : ∀ i : Fin 256, i.val.Prime → (199 < i.val) → (HardTail.denomWords i.val).2=0 := by decide +kernel
    exact all ⟨p,by omega⟩ pp large

include audit in
set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
theorem rank_correct {p n : ℕ} (pp : p.Prime) (large : 23<p) (hn : n≤43399) :
    rank p (negative p) (bases p) n =
      (Nat.primeCounting n : ℤ) - bitPrefix (HardTail.denomWords p).2 (n+1) := by
  by_cases small : p≤199
  · rw [rank,if_pos small,smallPi_correct hn,negRank_correct (small_mem pp large small) hn]
  · rw [rank,if_neg small,smallPi_correct hn,big_no_negative pp (by omega)]
    simp [bitPrefix]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem denom_succ (p n : ℕ) :
    denomWeight p (n+1) = denomWeight p n + (if p<(n+1).minFac then -moebius (n+1) else 0) := by
  unfold denomWeight
  rw [sum_filter,sum_filter]
  have up : Icc 1 (n+1)=insert (n+1) (Icc 1 n) := by
    ext i
    simp only [mem_Icc,mem_insert]
    omega
  rw [up,sum_insert (by simp)]
  by_cases sf : Squarefree (n+1)
  · simp only [sf,true_and,add_comm]
  · simp only [sf,false_and,if_false,moebius_eq_zero_of_not_squarefree sf,neg_zero,ite_self,zero_add,add_zero]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem pref_succ (w n : ℕ) : bitPrefix w (n+1) =
    bitPrefix w n + (if w.testBit n then 1 else 0) := by
  rw [prefix_add]
  by_cases bit : w.testBit n=true <;> simp [Finset.range_one,Finset.filter_singleton,bit]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem prime_succ (n : ℕ) : Nat.primeCounting (n+1) =
    Nat.primeCounting n + (if (n+1).Prime then 1 else 0) := by
  change Nat.count Nat.Prime ((n+1)+1) = Nat.count Nat.Prime (n+1) + _
  rw [Nat.count_succ]

include audit in
set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
private theorem rank_step {p n : ℕ} (pp : p.Prime) (large : 23<p) (cap : p≤3006)
    (pn : p≤n) (hn : n+1≤43399) :
    rank p (negative p) (bases p) (n+1) - rank p (negative p) (bases p) n =
      denomWeight p (n+1)-denomWeight p n := by
  have signed := HardTail.denomWords_correct (d:=n+1) pp large cap (by omega) hn
  rw [if_congr (posBit (p:=p) hn) rfl rfl] at signed
  rw [rank_correct pp large hn,rank_correct pp large (by omega),pref_succ _ (n+1),
    prime_succ,denom_succ,Nat.cast_add,Nat.cast_add]
  by_cases a : (n+1).Prime <;> by_cases b : (HardTail.denomWords p).2.testBit (n+1)=true <;>
    simp [a,b] at signed ⊢ <;> omega

include audit in
set_option maxRecDepth 131072 in
set_option maxHeartbeats 2000000 in
theorem rank_diff {p v u : ℕ} (pp : p.Prime) (large : 23<p) (cap : p≤3006)
    (pv : p≤v) (vu : v≤u) (top : u≤43399) :
    rank p (negative p) (bases p) u - rank p (negative p) (bases p) v =
      denomWeight p u - denomWeight p v := by
  have at_k (k : ℕ) (h : v+k≤43399) :
      rank p (negative p) (bases p) (v+k) - rank p (negative p) (bases p) v =
        denomWeight p (v+k) - denomWeight p v := by
    induction k with
    | zero => simp
    | succ k ih =>
      have prev := ih (by omega)
      have now := rank_step (n:=v+k) pp large cap (by omega) (by omega)
      change rank p (negative p) (bases p) (v+k+1) - _ = denomWeight p (v+k+1)-_
      omega
  have eq : v+(u-v)=u := by omega
  simpa only [eq] using at_k (u-v) (by omega)

end Astra247824.FullLookup

namespace Astra247824.FullLookup
open Finset Leaves SquareBand
abbrev allPrimes := HardTail.Scan.roster

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem fullRoster : basePrimes.reverse ++ roster.map Entry.p = allPrimes := by rfl

theorem primeMem (p : ℕ) : p ∈ allPrimes ↔ p ≤ 3006 ∧ p.Prime := HardTail.Scan.roster_mem p
theorem ordered : allPrimes.Pairwise (· < ·) := HardTail.Scan.roster_sorted
theorem past_mem {ps later : List ℕ} {p q : ℕ}
    (part : ps.reverse ++ p::later = allPrimes) : q ∈ ps ↔ q ∈ descendingPrimes (p-1) := by
  have sorted : (ps.reverse ++ p::later).Pairwise (· < ·) := part ▸ ordered
  obtain ⟨_, next, before⟩ := List.pairwise_append.mp sorted
  have pm := (primeMem p).mp (part ▸ List.mem_append_right _ List.mem_cons_self)
  rw [mem_descending,Nat.mem_primesLE]
  constructor
  · intro qIn
    have prev := List.mem_reverse.mpr qIn
    have qm := (primeMem q).mp (part ▸ List.mem_append_left _ prev)
    have less := before q prev p List.mem_cons_self
    exact ⟨by omega,qm.2⟩
  · rintro ⟨bound,pq⟩
    have less : q < p := by have := pm.2.pos; omega
    have qm := (primeMem q).mpr ⟨by omega,pq⟩
    rw [←part,List.mem_append,List.mem_cons] at qm
    rcases qm with h|h|h
    · exact List.mem_reverse.mp h
    · omega
    · exact (less.not_ge ((List.pairwise_cons.mp next).1 q h).le).elim

theorem count_congr {ps qs : List ℕ} (h : ∀ p, p∈ps ↔ p∈qs) (lo w : ℕ) :
    segmentCount ps lo w = segmentCount qs lo w := by
  simp only [segmentCount,h]

theorem baseRank (lo : ℕ) :
    smallRank 7 (lo+65535) - smallRank 7 (lo-1) = segmentCount basePrimes lo W := by
  have list_eq : descendingPrimes 18 = basePrimes := by decide +kernel
  have ranks (t : ℕ) : smallRank 7 t = segmentCount basePrimes 1 t := by
    have a := smallRank_signed (7 : Fin 8) t
    change (smallRank 7 t : ℤ) = signedSieve (descendingPrimes 18) t at a
    rw [list_eq,signedSieve_eq_segment] at a
    exact_mod_cast a
  rw [ranks,ranks]
  by_cases z : lo=0
  · subst lo
    have h := segmentCount_add basePrimes 0 1 65535
    rw [segmentCount_zero_head,if_neg (by decide : basePrimes ≠ []),Nat.zero_add,Nat.zero_add] at h
    have empty : segmentCount basePrimes 1 0 = 0 := by simp [segmentCount]
    simpa only [Nat.zero_add,Nat.zero_sub,empty,Nat.sub_zero] using h.symm
  · have h := segmentCount_add basePrimes 1 (lo-1) W
    have a : 1+(lo-1)=lo := by omega
    have v : (lo-1)+W=lo+65535 := by change (lo-1)+65536=lo+65535; omega
    rw [a,v] at h
    omega


end Astra247824.FullLookup

namespace Astra247824.FullLookup
open Finset Leaves SquareBand
abbrev Representation := ∀ {e : Entry}, e∈roster → e = make e.p (rawPattern e.p)
abbrev Coefficients := ∀ (b p pat : ℕ), p.Prime → p ≤ 3006 →
  coeff (make p pat) (X/((b+1)*W)) = weight p b

theorem capacity_zero (b p pat cap : ℕ) (small : cap < p*p) (pp : p.Prime) :
    coeff (make p pat) cap = 0 := by
  have limit := (Nat.div_lt_iff_lt_mul pp.pos).mpr small
  have empty : min (min 43399 (81744924555066/p^3)) (cap/p) ≤ max p (43399/p) :=
    (min_le_right ..).trans (limit.le.trans (le_max_left ..))
  change (if p ≤ 23 then 0 else
    if min (min 43399 (81744924555066/p^3)) (cap/p) ≤ max p (43399/p) then 0 else _) = 0
  simp only [if_pos empty, ite_self]

theorem zero_sum {l : List Entry} {f : Entry → ℤ} (h : ∀ e ∈ l, f e=0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons,List.sum_cons,h _ List.mem_cons_self,
      ih (fun e he => h e (List.mem_cons_of_mem _ he)),zero_add]

theorem run_correct (rep : Representation) (coeffs : Coefficients) (b : ℕ)
    (todo : List Entry) (ps : List ℕ) (s : ℕ × ℕ) (z : ℤ)
    (members : ∀ e ∈ todo, e∈roster)
    (part : ps.reverse ++ todo.map Entry.p = allPrimes)
    (lower : ∀ e ∈ todo, 19 ≤ e.p)
    (inv : stageInvariant s ps (b*W) W) :
    accumulate (b*W) (X/((b+1)*W)) s.1 s.2 z todo = z + (todo.map (fun e => cell e.p b)).sum := by
  induction todo generalizing ps s z with
  | nil => simp [accumulate]
  | cons e es ih =>
    let cap := X/((b+1)*W)
    have split : ps.reverse ++ e.p :: es.map Entry.p = allPrimes := part
    have entry_prime (q : Entry) (hq : q∈e::es) : q.p ≤ 3006 ∧ q.p.Prime :=
      (primeMem q.p).mp (part ▸ List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    have good := entry_prime e List.mem_cons_self
    have hw := rep (members e List.mem_cons_self)
    have pat : e.pat = fixedPattern e.p W := (congrArg Entry.pat hw).trans (rawPattern_eq _)
    have modulus : e.mod = 2^e.p-1 := by
      have h := congrArg Entry.mod hw
      simpa only [make,Nat.shiftLeft_eq,one_mul] using h
    have coefficient : coeff e cap = weight e.p b :=
      (congrArg (fun ent => coeff ent cap) hw).trans (coeffs b e.p _ good.2 good.1)
    have bitRange := lower e List.mem_cons_self
    by_cases done : cap < e.p*e.p
    · have order : (e.p :: es.map Entry.p).Pairwise (· < ·) :=
        (List.pairwise_append.mp (split ▸ ordered)).2.1
      have zero : ((e::es).map (fun a => cell a.p b)).sum=0 := by
        apply zero_sum
        intro q hq
        have next : e.p ≤ q.p := by
          rcases List.mem_cons.mp hq with rfl|tail
          · rfl
          · exact ((List.pairwise_cons.mp order).1 _ (List.mem_map.mpr ⟨q,tail,rfl⟩)).le
        have facts := entry_prime q hq
        have absent := (coeffs b q.p 0 facts.2 facts.1).symm.trans
          (capacity_zero b q.p 0 cap (done.trans_le (Nat.mul_self_le_mul_self next)) facts.2)
        simp only [cell,absent,mul_zero]
      rw [accumulate,if_pos done,zero,add_zero]
    · have enough : W/e.p+2 < 2^e.p-1 := by
        have den : W/e.p ≤ W/19 := Nat.div_le_div_left bitRange (by decide)
        have powBound := Nat.pow_le_pow_right (by decide : 0 < 2) bitRange
        change W/e.p+2 < 2^e.p-1
        have k : W/19+2 < 2^19-1 := by decide
        omega
      let s' := stageUpdate s.1 s.2 e.pat e.mod e.p (b*W)
      have forward : stageInvariant s' (e.p::ps) (b*W) W := by
        dsimp only [s']; rw [pat,modulus]; exact stageInvariant_step inv good.2.pos enough
      have next : (e.p::ps).reverse ++ es.map Entry.p = allPrimes := by
        simpa [List.reverse_cons,List.append_assoc] using split
      have update := ih (e.p::ps) s' (z+(s.2:ℤ)*coeff e cap)
        (fun q hq => members q (List.mem_cons_of_mem e hq)) next
        (fun q hq => lower q (List.mem_cons_of_mem e hq)) forward
      have count : s.2 = segmentCount (descendingPrimes (e.p-1)) (b*W) W :=
        inv.2.2.trans (count_congr (fun _ => past_mem split) _ _)
      rw [accumulate,if_neg done]
      change accumulate _ _ s'.1 s'.2 _ es = _
      rw [update,coefficient,count,List.map_cons,List.sum_cons,cell,add_assoc]


end Astra247824.FullLookup

/- Connect the row evaluator to the weighted prime sum in the complete blocks. -/
namespace Astra247824.FullLookup
open Finset Leaves SquareBand
theorem roster_order : (roster.map Entry.p).Pairwise (· < ·) :=
  (List.pairwise_append.mp (fullRoster ▸ ordered)).2.1

theorem in_roster (p : ℕ) : p ∈ roster.map Entry.p ↔ 17 < p ∧ p ≤ 3006 ∧ p.Prime := by
  have maxBase : ∀ q ∈ basePrimes, q ≤ 17 := by decide
  have last : 17 ∈ basePrimes.reverse := by decide
  constructor
  · intro h
    have props := (primeMem p).mp (fullRoster ▸ List.mem_append_right _ h)
    exact ⟨(List.pairwise_append.mp (fullRoster ▸ ordered)).2.2 17 last p h,props⟩
  · rintro ⟨lo,cap,pp⟩
    have h := (primeMem p).mpr ⟨cap,pp⟩
    rw [←fullRoster,List.mem_append] at h
    exact h.resolve_left (fun x => lo.not_ge (maxBase p (List.mem_reverse.mp x)))

/- One full sweep computes exactly the contribution of the complete block. -/
theorem row_eq_cells (rep : Representation) (coefs : Coefficients) (b : ℕ) :
    row b = ∑ p ∈ stages, cell p b := by
  have lower (e : Entry) (mem : e∈roster) : 19 ≤ e.p := by
    have a := (in_roster e.p).mp (List.mem_map.mpr ⟨e,mem,rfl⟩)
    by_contra! below
    have eq : e.p=18 := by omega
    exact (by decide : ¬Nat.Prime 18) (eq ▸ a.2.2)
  have pos : ∀ p ∈ basePrimes, 0<p := by decide
  have h := run_correct rep coefs b roster basePrimes _ 0 (fun _ m => m) fullRoster lower
    (stageInvariant_start (b*W) W _ pos (baseRank _))
  have incl : stages ⊆ (roster.map Entry.p).toFinset := by
    intro p hp
    obtain ⟨e,he,eq⟩ := mem_image.mp hp
    have facts := Nat.mem_primesLE.mp (SquareBand.stage_subset hp)
    exact List.mem_toFinset.mpr ((in_roster p).mpr ⟨by have := (mem_filter.mp he).2; omega,facts⟩)
  have outside {p : ℕ} (hp : p ∉ stages) : cell p b = 0 := by
    change (segmentCount (descendingPrimes (p-1)) (b*W) W : ℤ) * weight p b = 0
    rw [SquareBand.absent hp b, mul_zero]
  have extend := sum_subset incl (f:=fun p => cell p b) (fun _ _ hp => outside hp)
  rw [extend,List.sum_toFinset _ roster_order.nodup,List.map_map]
  simpa only [row,zero_add,Function.comp_def] using h

/- The checked arithmetic sum gives the public full-block statement. -/
theorem h3_of_rows (rep : Representation) (coefs : Coefficients)
    (checked : (∑ b ∈ range 28740, row b) = 3360343589286) :
    OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H3 :=
  SquareBand.h3_iff_cells.mpr ((sum_congr rfl (fun b _ => (row_eq_cells rep coefs b).symm)).trans checked)


end Astra247824.FullLookup

/- The numerical weight in every stage is the coefficient in the published complete-block sum. -/
namespace Astra247824.FullLookup
open Finset Leaves ArithmeticFunction
open SquareBand (X Y W)

/- Every stage carries its certified pattern and its prescribed denominator data. -/
set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
theorem roster_entry {e : Entry} (h : e∈roster) : e = make e.p (rawPattern e.p) := by
  have eq : roster = roster.map (fun a => make a.p (rawPattern a.p)) := by rfl
  rw [eq] at h
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
  rfl

set_option maxRecDepth 131072 in
set_option maxHeartbeats 10000000 in
theorem coeff_of_tables [CheckedWeights] (b p pat : ℕ) (pp : p.Prime) (cap : p≤3006) :
    coeff (make p pat) (X/((b+1)*W)) = SquareBand.weight p b := by
  by_cases small : p≤23
  · change (if p≤23 then 0 else _) = _
    rw [if_pos small]
    symm
    unfold SquareBand.weight
    apply sum_eq_zero
    intro e he
    have a := (mem_filter.mp (mem_filter.mp he).1).2
    have b := (mem_filter.mp he).2.1
    omega
  have large : 23<p := by omega
  have same : SquareBand.S.filter (fun e => e.2=p ∧ b<(X/(e.1*e.2))/W) =
      (hardEdges X Y).filter (fun e => e.2=p ∧ b<(X/(e.1*e.2))/W) := by
    ext e
    simp only [SquareBand.S,mem_filter]
    constructor
    · exact fun ⟨⟨h,_⟩,rest⟩ => ⟨h,rest⟩
    · exact fun ⟨h,eq,l⟩ => ⟨⟨h,by omega⟩,eq,l⟩
  rw [SquareBand.weight,same,weighted_mixed_rank pp (by decide : 0<W)]
  let v := max p (Y/p)
  let u := lateTop X Y p W b
  have high : u≤Y := (min_le_left ..).trans (min_le_left ..)
  have upper : min (min Y (X/p^3)) (X/((b+1)*W)/p) = u := by
    simp only [u,lateTop,Nat.div_div_eq_div_mul,Nat.mul_comm ((b+1)*W)]
  change (if p≤23 then 0 else
    if min (min Y (X/p^3)) (X/((b+1)*W)/p)≤v then 0 else
      rank p (negative p) (bases p) (min (min Y (X/p^3)) (X/((b+1)*W)/p)) -
        rank p (negative p) (bases p) v) = denomWeight p u-denomWeight p (min u v)
  rw [if_neg small,upper]
  by_cases below : u≤v
  · rw [if_pos below,min_eq_left below,sub_self]
  · rw [if_neg below,min_eq_right (by omega : v≤u)]
    exact rank_diff pp large cap (le_max_left ..) (by omega) high

end Astra247824.FullLookup

/- Binary intervals and their telescoping verification in the full block lattice. -/
namespace Astra247824.FullLookup
open Finset

def rowPrefix (n : ℕ) : ℤ := ∑ b ∈ range n, row b

theorem interval_diff (k i : ℕ) : interval k i = rowPrefix (i+2^k) - rowPrefix i := by
  induction k generalizing i with
  | zero => simp [interval,rowPrefix,sum_range_succ]
  | succ k ih =>
    rw [interval,ih,ih,Nat.shiftLeft_eq,Nat.one_mul]
    have pos : i+2^k+2^k=i+2^(k+1) := by rw [pow_succ]; omega
    rw [pos]
    omega

theorem join_values {k i : ℕ} {a b c : ℤ} (left : interval k i=a)
    (right : interval k (i+(1 <<< k))=b) (value : a+b=c := by decide) :
    interval (k+1) i=c := by rw [interval,left,right,value]
end Astra247824.FullLookup

namespace Astra247824.FullLookup

private def baseAtZero (width : ℕ) : List ℕ → ℕ
  | [] => (1 <<< width)-1
  | p::ps =>
    let tail := baseAtZero width ps
    let pat := ((1 <<< (p*(width/p+1)))-1)/((1 <<< p)-1)
    tail ^^^ (tail &&& pat)

private theorem baseAtZero_eq (width : ℕ) (ps : List ℕ) :
    baseAtZero width ps = blockMask 0 width ps := by
  induction ps with
  | nil => simp [baseAtZero,blockMask,Nat.one_shiftLeft]
  | cons p ps ih =>
    simp only [baseAtZero,blockMask,ih,clearDivisors,packedDivisors,Nat.zero_mod,Nat.zero_add,
      Nat.shiftRight_zero,Nat.one_shiftLeft]

private def wheelWord : {w : ℕ // blockMask 0 (510510+65536) basePrimes = w} :=
  ⟨_, (baseAtZero_eq _ _).symm.trans (by conv => lhs; whnf)⟩

private def lowBits : {w : ℕ // (1 <<< 65536)-1 = w} := ⟨_, by conv => lhs; whnf⟩

def baseWindow (lo : ℕ) : ℕ := (wheelWord.1 >>> (lo%510510)) &&& lowBits.1

/- Every multiple of a base prime has the same residue over a full 510,510-integer period. -/
theorem window_eq_blockMask (lo : ℕ) : baseWindow lo = blockMask lo 65536 basePrimes := by
  have factors : ∀ p ∈ basePrimes, p ∣ 510510 := by decide
  have positive : ∀ p ∈ basePrimes, 0<p := by decide
  have bits : lowBits.1 = 2^65536-1 := by rw [←lowBits.property,Nat.one_shiftLeft]
  apply Nat.eq_iff_testBit_eq.mpr
  intro i
  rw [baseWindow,bits,Nat.and_two_pow_sub_one_eq_mod,Nat.testBit_mod_two_pow]
  by_cases hi : i<65536
  · rw [decide_eq_true hi,Bool.true_and,Nat.testBit_shiftRight,←wheelWord.property]
    have pos : lo%510510+i < 510510+65536 := by
      have rem := Nat.mod_lt lo (by decide : 0<510510)
      omega
    apply Bool.eq_iff_iff.mpr
    rw [blockMask_spec pos positive,blockMask_spec hi positive,Nat.zero_add]
    have cycle (p : ℕ) (hp : p∈basePrimes) : p ∣ lo%510510+i ↔ p ∣ lo+i := by
      have multiple : p ∣ 510510*(lo/510510) := dvd_mul_of_dvd_left (factors p hp) _
      simpa only [←Nat.add_assoc,Nat.div_add_mod] using
        (@Nat.dvd_add_iff_right p (510510*(lo/510510)) (lo%510510+i) multiple)
    exact ⟨fun h p hp d => h p hp ((cycle p hp).mpr d), fun h p hp d => h p hp ((cycle p hp).mp d)⟩
  · have bound := (stageInvariant_start lo 65536 (segmentCount basePrimes lo 65536) positive rfl).1
    have outside := Nat.testBit_lt_two_pow (i:=i)
      (bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [decide_eq_false hi,Bool.false_and,outside]

def windowRow (b : ℕ) : ℤ :=
  let lo := b*65536
  let alive := smallRank 7 (lo+65535) - smallRank 7 (lo-1)
  accumulate lo (81744924555066/((b+1)*65536)) (baseWindow lo) alive 0 roster

theorem windowRow_eq (b : ℕ) : windowRow b = row b := by
  simp only [windowRow,row,window_eq_blockMask]

def windowInterval : ℕ → ℕ → ℤ
  | 0, i => windowRow i
  | k+1, i => windowInterval k i + windowInterval k (i+(1 <<< k))

theorem windowInterval_eq (k i : ℕ) : windowInterval k i = interval k i := by
  induction k generalizing i with
  | zero => exact windowRow_eq i
  | succ k ih => simp only [windowInterval,interval,ih]

end Astra247824.FullLookup

/- Consecutive dyadic intervals, with one nonnegative numerical value in each fixed-width lane. -/
namespace Astra247824.FullLookup

def tilesMatch (depth width : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | count+1, start, word =>
    decide (windowInterval depth start = ((word % 2^width : ℕ) : ℤ)) &&
      tilesMatch depth width count (start+2^depth) (word >>> width)

def tileSum (width : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | count+1, word => word % 2^width + tileSum width count (word >>> width)

theorem checked_tiles (depth width count start word : ℕ)
    (checked : tilesMatch depth width count start word = true) :
    rowPrefix (start+count*2^depth) - rowPrefix start = (tileSum width count word : ℤ) := by
  induction count generalizing start word with
  | zero => simp [tileSum]
  | succ count ih =>
    obtain ⟨first, remaining⟩ := Bool.and_eq_true_iff.mp checked
    have curr := of_decide_eq_true first
    rw [windowInterval_eq,interval_diff] at curr
    have rest := ih _ _ remaining
    have bound : start + (count+1)*2^depth = (start+2^depth)+count*2^depth := by
      rw [Nat.succ_mul]; omega
    rw [bound, tileSum, Nat.cast_add]
    omega

/- Groups combine by their common endpoint, so an intermediate running total need not be stored. -/
theorem append_tile_sum {start middle stop : ℕ} {x y : ℤ}
    (first : rowPrefix middle - rowPrefix start = x)
    (rest : rowPrefix stop - rowPrefix middle = y) :
    rowPrefix stop - rowPrefix start = x+y := by omega

end Astra247824.FullLookup

namespace Astra247824.FullLookup
set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
def smallPrimesWord : Nat := 0xa28028208820a00a08800228a20208828828208a20a08a28ac

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
def factorial209 : Nat := 0x5a2f13c9dbd1dd462b403a7390b858ab41f680af9959437ae0227726c437cbee345f3ea00d9ec04427d7f0b6608ce5a2bece2de63122ea9e58d5b351854a0ad772328c31be048bcc69d381a75a0f45f46d3007ac9362a4cfaab0eaf1750bc23ecf55775741271a43464522ac5490a6a94d9f94d7afd4cb171f1a4f85487bf0e01bfd28576a412f3456a302000000000000000000000000000000000000000000000000000

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
def primeFlag (n : Nat) : Bool :=
  if n ≤ 209 then smallPrimesWord.testBit n else n.gcd factorial209 == 1

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
def rankStep (n : Nat) : Bool :=
  if 43399 < n then true else
    let previous := if n = 0 then 0 else smallPi (n-1)
    (smallPi n == previous + (if primeFlag n then 1 else 0)) &&
      ((HardTail.denomWords 29).1.testBit n == primeFlag n)

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
def offsetStep (p q : Nat) : Bool :=
  if q < 678 then offset (bases p) (q+1) == offset (bases p) q +
    GlobalRank.pop64 (wordPiece (negative p) (64*q) 64) else true



set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc0 : PLift (gridTree rankStep 9 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc512 : PLift (gridTree rankStep 9 512 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc1024 : PLift (gridTree rankStep 9 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc1536 : PLift (gridTree rankStep 9 1536 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc2048 : PLift (gridTree rankStep 9 2048 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc2560 : PLift (gridTree rankStep 9 2560 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc3072 : PLift (gridTree rankStep 9 3072 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc3584 : PLift (gridTree rankStep 9 3584 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc4096 : PLift (gridTree rankStep 9 4096 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc4608 : PLift (gridTree rankStep 9 4608 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc5120 : PLift (gridTree rankStep 9 5120 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc5632 : PLift (gridTree rankStep 9 5632 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc6144 : PLift (gridTree rankStep 9 6144 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc6656 : PLift (gridTree rankStep 9 6656 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc7168 : PLift (gridTree rankStep 9 7168 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc7680 : PLift (gridTree rankStep 9 7680 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc8192 : PLift (gridTree rankStep 9 8192 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc8704 : PLift (gridTree rankStep 9 8704 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc9216 : PLift (gridTree rankStep 9 9216 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc9728 : PLift (gridTree rankStep 9 9728 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc10240 : PLift (gridTree rankStep 9 10240 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc10752 : PLift (gridTree rankStep 9 10752 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc11264 : PLift (gridTree rankStep 9 11264 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc11776 : PLift (gridTree rankStep 9 11776 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc12288 : PLift (gridTree rankStep 9 12288 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc12800 : PLift (gridTree rankStep 9 12800 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc13312 : PLift (gridTree rankStep 9 13312 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc13824 : PLift (gridTree rankStep 9 13824 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc14336 : PLift (gridTree rankStep 9 14336 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc14848 : PLift (gridTree rankStep 9 14848 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc15360 : PLift (gridTree rankStep 9 15360 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc15872 : PLift (gridTree rankStep 9 15872 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc16384 : PLift (gridTree rankStep 9 16384 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc16896 : PLift (gridTree rankStep 9 16896 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc17408 : PLift (gridTree rankStep 9 17408 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc17920 : PLift (gridTree rankStep 9 17920 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc18432 : PLift (gridTree rankStep 9 18432 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc18944 : PLift (gridTree rankStep 9 18944 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc19456 : PLift (gridTree rankStep 9 19456 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc19968 : PLift (gridTree rankStep 9 19968 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc20480 : PLift (gridTree rankStep 9 20480 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc20992 : PLift (gridTree rankStep 9 20992 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc21504 : PLift (gridTree rankStep 9 21504 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc22016 : PLift (gridTree rankStep 9 22016 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc22528 : PLift (gridTree rankStep 9 22528 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc23040 : PLift (gridTree rankStep 9 23040 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc23552 : PLift (gridTree rankStep 9 23552 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc24064 : PLift (gridTree rankStep 9 24064 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc24576 : PLift (gridTree rankStep 9 24576 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc25088 : PLift (gridTree rankStep 9 25088 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc25600 : PLift (gridTree rankStep 9 25600 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc26112 : PLift (gridTree rankStep 9 26112 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc26624 : PLift (gridTree rankStep 9 26624 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc27136 : PLift (gridTree rankStep 9 27136 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc27648 : PLift (gridTree rankStep 9 27648 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc28160 : PLift (gridTree rankStep 9 28160 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc28672 : PLift (gridTree rankStep 9 28672 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc29184 : PLift (gridTree rankStep 9 29184 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc29696 : PLift (gridTree rankStep 9 29696 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc30208 : PLift (gridTree rankStep 9 30208 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc30720 : PLift (gridTree rankStep 9 30720 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc31232 : PLift (gridTree rankStep 9 31232 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc31744 : PLift (gridTree rankStep 9 31744 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc32256 : PLift (gridTree rankStep 9 32256 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc32768 : PLift (gridTree rankStep 9 32768 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc33280 : PLift (gridTree rankStep 9 33280 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc33792 : PLift (gridTree rankStep 9 33792 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc34304 : PLift (gridTree rankStep 9 34304 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc34816 : PLift (gridTree rankStep 9 34816 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc35328 : PLift (gridTree rankStep 9 35328 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc35840 : PLift (gridTree rankStep 9 35840 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc36352 : PLift (gridTree rankStep 9 36352 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc36864 : PLift (gridTree rankStep 9 36864 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc37376 : PLift (gridTree rankStep 9 37376 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc37888 : PLift (gridTree rankStep 9 37888 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc38400 : PLift (gridTree rankStep 9 38400 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc38912 : PLift (gridTree rankStep 9 38912 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc39424 : PLift (gridTree rankStep 9 39424 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc39936 : PLift (gridTree rankStep 9 39936 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc40448 : PLift (gridTree rankStep 9 40448 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc40960 : PLift (gridTree rankStep 9 40960 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc41472 : PLift (gridTree rankStep 9 41472 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc41984 : PLift (gridTree rankStep 9 41984 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc42496 : PLift (gridTree rankStep 9 42496 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc43008 : PLift (gridTree rankStep 9 43008 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc43520 : PLift (gridTree rankStep 9 43520 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc44032 : PLift (gridTree rankStep 9 44032 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc44544 : PLift (gridTree rankStep 9 44544 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc45056 : PLift (gridTree rankStep 9 45056 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc45568 : PLift (gridTree rankStep 9 45568 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc46080 : PLift (gridTree rankStep 9 46080 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc46592 : PLift (gridTree rankStep 9 46592 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc47104 : PLift (gridTree rankStep 9 47104 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc47616 : PLift (gridTree rankStep 9 47616 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc48128 : PLift (gridTree rankStep 9 48128 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc48640 : PLift (gridTree rankStep 9 48640 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc49152 : PLift (gridTree rankStep 9 49152 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc49664 : PLift (gridTree rankStep 9 49664 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc50176 : PLift (gridTree rankStep 9 50176 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc50688 : PLift (gridTree rankStep 9 50688 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc51200 : PLift (gridTree rankStep 9 51200 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc51712 : PLift (gridTree rankStep 9 51712 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc52224 : PLift (gridTree rankStep 9 52224 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc52736 : PLift (gridTree rankStep 9 52736 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc53248 : PLift (gridTree rankStep 9 53248 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc53760 : PLift (gridTree rankStep 9 53760 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc54272 : PLift (gridTree rankStep 9 54272 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc54784 : PLift (gridTree rankStep 9 54784 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc55296 : PLift (gridTree rankStep 9 55296 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc55808 : PLift (gridTree rankStep 9 55808 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc56320 : PLift (gridTree rankStep 9 56320 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc56832 : PLift (gridTree rankStep 9 56832 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc57344 : PLift (gridTree rankStep 9 57344 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc57856 : PLift (gridTree rankStep 9 57856 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc58368 : PLift (gridTree rankStep 9 58368 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc58880 : PLift (gridTree rankStep 9 58880 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc59392 : PLift (gridTree rankStep 9 59392 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc59904 : PLift (gridTree rankStep 9 59904 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc60416 : PLift (gridTree rankStep 9 60416 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc60928 : PLift (gridTree rankStep 9 60928 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc61440 : PLift (gridTree rankStep 9 61440 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc61952 : PLift (gridTree rankStep 9 61952 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc62464 : PLift (gridTree rankStep 9 62464 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc62976 : PLift (gridTree rankStep 9 62976 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc63488 : PLift (gridTree rankStep 9 63488 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc64000 : PLift (gridTree rankStep 9 64000 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc64512 : PLift (gridTree rankStep 9 64512 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def prc65024 : PLift (gridTree rankStep 9 65024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private theorem rank_16_0 : gridTree rankStep 16 0 = true := (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair prc0.down prc512.down) (grid_pair prc1024.down prc1536.down)) (grid_pair (grid_pair prc2048.down prc2560.down) (grid_pair prc3072.down prc3584.down))) (grid_pair (grid_pair (grid_pair prc4096.down prc4608.down) (grid_pair prc5120.down prc5632.down)) (grid_pair (grid_pair prc6144.down prc6656.down) (grid_pair prc7168.down prc7680.down)))) (grid_pair (grid_pair (grid_pair (grid_pair prc8192.down prc8704.down) (grid_pair prc9216.down prc9728.down)) (grid_pair (grid_pair prc10240.down prc10752.down) (grid_pair prc11264.down prc11776.down))) (grid_pair (grid_pair (grid_pair prc12288.down prc12800.down) (grid_pair prc13312.down prc13824.down)) (grid_pair (grid_pair prc14336.down prc14848.down) (grid_pair prc15360.down prc15872.down))))) (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair prc16384.down prc16896.down) (grid_pair prc17408.down prc17920.down)) (grid_pair (grid_pair prc18432.down prc18944.down) (grid_pair prc19456.down prc19968.down))) (grid_pair (grid_pair (grid_pair prc20480.down prc20992.down) (grid_pair prc21504.down prc22016.down)) (grid_pair (grid_pair prc22528.down prc23040.down) (grid_pair prc23552.down prc24064.down)))) (grid_pair (grid_pair (grid_pair (grid_pair prc24576.down prc25088.down) (grid_pair prc25600.down prc26112.down)) (grid_pair (grid_pair prc26624.down prc27136.down) (grid_pair prc27648.down prc28160.down))) (grid_pair (grid_pair (grid_pair prc28672.down prc29184.down) (grid_pair prc29696.down prc30208.down)) (grid_pair (grid_pair prc30720.down prc31232.down) (grid_pair prc31744.down prc32256.down)))))) (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair prc32768.down prc33280.down) (grid_pair prc33792.down prc34304.down)) (grid_pair (grid_pair prc34816.down prc35328.down) (grid_pair prc35840.down prc36352.down))) (grid_pair (grid_pair (grid_pair prc36864.down prc37376.down) (grid_pair prc37888.down prc38400.down)) (grid_pair (grid_pair prc38912.down prc39424.down) (grid_pair prc39936.down prc40448.down)))) (grid_pair (grid_pair (grid_pair (grid_pair prc40960.down prc41472.down) (grid_pair prc41984.down prc42496.down)) (grid_pair (grid_pair prc43008.down prc43520.down) (grid_pair prc44032.down prc44544.down))) (grid_pair (grid_pair (grid_pair prc45056.down prc45568.down) (grid_pair prc46080.down prc46592.down)) (grid_pair (grid_pair prc47104.down prc47616.down) (grid_pair prc48128.down prc48640.down))))) (grid_pair (grid_pair (grid_pair (grid_pair (grid_pair prc49152.down prc49664.down) (grid_pair prc50176.down prc50688.down)) (grid_pair (grid_pair prc51200.down prc51712.down) (grid_pair prc52224.down prc52736.down))) (grid_pair (grid_pair (grid_pair prc53248.down prc53760.down) (grid_pair prc54272.down prc54784.down)) (grid_pair (grid_pair prc55296.down prc55808.down) (grid_pair prc56320.down prc56832.down)))) (grid_pair (grid_pair (grid_pair (grid_pair prc57344.down prc57856.down) (grid_pair prc58368.down prc58880.down)) (grid_pair (grid_pair prc59392.down prc59904.down) (grid_pair prc60416.down prc60928.down))) (grid_pair (grid_pair (grid_pair prc61440.down prc61952.down) (grid_pair prc62464.down prc62976.down)) (grid_pair (grid_pair prc63488.down prc64000.down) (grid_pair prc64512.down prc65024.down)))))))

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem rank_step_checked (n : Nat) (hn : n ≤ 43399) :
    smallPi n = (if n = 0 then 0 else smallPi (n-1)) + (if primeFlag n then 1 else 0) ∧
      (HardTail.denomWords 29).1.testBit n = primeFlag n := by
  have h := grid_index rank_16_0 (d := n) (Nat.zero_le _) (by change n < 65536; omega)
  simpa only [rankStep, if_neg (by omega : ¬43399 < n), Bool.and_eq_true, beq_iff_eq] using h



set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem prime_flag_correct (n : ℕ) (hn : n ≤ 43399) : primeFlag n = true ↔ n.Prime := by
  by_cases small : n ≤ 209
  · have table : ∀ i : Fin 210, smallPrimesWord.testBit i.val = true ↔ i.val.Prime := by decide +kernel
    simpa only [primeFlag, if_pos small] using table ⟨n, by omega⟩
  · have factorial_eq : factorial209 = Nat.factorial 209 := by decide +kernel
    simp only [primeFlag, if_neg small, beq_iff_eq, factorial_eq]
    change n.Coprime (Nat.factorial 209) ↔ n.Prime
    constructor
    · intro coprime
      by_contra composite
      have lower := (Nat.coprime_factorial_iff (by omega : n ≠ 1)).mp coprime
      have upper := (Nat.minFac_sq_le_self (by omega : 0 < n) composite).trans
        (show n ≤ 209^2 by omega)
      exact (Nat.not_lt_of_ge upper) (Nat.pow_lt_pow_left lower (by decide : 2 ≠ 0))
    · exact fun prime => prime.coprime_factorial_of_lt (by omega)

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem compact_prime_count (n : ℕ) (hn : n ≤ 43399) : smallPi n = Nat.primeCounting n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have step := (rank_step_checked (n+1) hn).1
    have flag := prime_flag_correct (n+1) hn
    have count := Nat.count_succ Nat.Prime (n+1)
    change Nat.primeCounting (n+1) = Nat.primeCounting n + _ at count
    simpa only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, ih (by omega), flag, count] using step

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem compact_prime_bit (n : ℕ) (hn : n ≤ 43399) : (HardTail.denomWords 29).1.testBit n = true ↔ n.Prime := by
  rw [(rank_step_checked n hn).2]
  exact prime_flag_correct n hn



set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po29 : PLift (gridTree (offsetStep 29) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po31 : PLift (gridTree (offsetStep 31) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po37 : PLift (gridTree (offsetStep 37) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po41 : PLift (gridTree (offsetStep 41) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po43 : PLift (gridTree (offsetStep 43) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po47 : PLift (gridTree (offsetStep 47) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po53 : PLift (gridTree (offsetStep 53) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po59 : PLift (gridTree (offsetStep 59) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po61 : PLift (gridTree (offsetStep 61) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po67 : PLift (gridTree (offsetStep 67) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po71 : PLift (gridTree (offsetStep 71) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po73 : PLift (gridTree (offsetStep 73) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po79 : PLift (gridTree (offsetStep 79) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po83 : PLift (gridTree (offsetStep 83) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po89 : PLift (gridTree (offsetStep 89) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po97 : PLift (gridTree (offsetStep 97) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po101 : PLift (gridTree (offsetStep 101) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po103 : PLift (gridTree (offsetStep 103) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po107 : PLift (gridTree (offsetStep 107) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po109 : PLift (gridTree (offsetStep 109) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po113 : PLift (gridTree (offsetStep 113) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po127 : PLift (gridTree (offsetStep 127) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po131 : PLift (gridTree (offsetStep 131) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po137 : PLift (gridTree (offsetStep 137) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po139 : PLift (gridTree (offsetStep 139) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po149 : PLift (gridTree (offsetStep 149) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po151 : PLift (gridTree (offsetStep 151) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po157 : PLift (gridTree (offsetStep 157) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po163 : PLift (gridTree (offsetStep 163) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po167 : PLift (gridTree (offsetStep 167) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po173 : PLift (gridTree (offsetStep 173) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po179 : PLift (gridTree (offsetStep 179) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po181 : PLift (gridTree (offsetStep 181) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po191 : PLift (gridTree (offsetStep 191) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po193 : PLift (gridTree (offsetStep 193) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po197 : PLift (gridTree (offsetStep 197) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
private def po199 : PLift (gridTree (offsetStep 199) 10 0 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem checkedNeg {p : Nat} (hp : p ∈ smallPrimes) : negative p = (HardTail.denomWords p).2 := by
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem checkedZero {p : Nat} (hp : p ∈ smallPrimes) : offset (bases p) 0 = 0 := by
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem checkedNext {p q : Nat} (hp : p ∈ smallPrimes) (hq : q < 678) :
    offset (bases p) (q+1) = offset (bases p) q + GlobalRank.pop64 (wordPiece (negative p) (64*q) 64) := by
  have checked : gridTree (offsetStep p) 10 0 = true := by
    simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact po29.down
    · exact po31.down
    · exact po37.down
    · exact po41.down
    · exact po43.down
    · exact po47.down
    · exact po53.down
    · exact po59.down
    · exact po61.down
    · exact po67.down
    · exact po71.down
    · exact po73.down
    · exact po79.down
    · exact po83.down
    · exact po89.down
    · exact po97.down
    · exact po101.down
    · exact po103.down
    · exact po107.down
    · exact po109.down
    · exact po113.down
    · exact po127.down
    · exact po131.down
    · exact po137.down
    · exact po139.down
    · exact po149.down
    · exact po151.down
    · exact po157.down
    · exact po163.down
    · exact po167.down
    · exact po173.down
    · exact po179.down
    · exact po181.down
    · exact po191.down
    · exact po193.down
    · exact po197.down
    · exact po199.down
  have step := grid_index checked (d := q) (Nat.zero_le _) (by change q < 1024; omega)
  simpa only [offsetStep, if_pos hq, beq_iff_eq] using step


set_option maxRecDepth 131072 in
set_option maxHeartbeats 20000000 in
theorem direct_weights : CheckedWeights where
  grid := fun hn => ⟨compact_prime_count _ hn, compact_prime_bit _ hn⟩
  word := fun hp => checkedNeg hp
  zero := fun hp => checkedZero hp
  next := fun hp hq => checkedNext hp hq
end Astra247824.FullLookup


namespace Astra247824.SquareBand
open Finset Leaves ArithmeticFunction
theorem original_row_value [FullLookup.CheckedWeights] (b : ℕ) :
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun b : ℕ => ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1)
  f b = FullLookup.row b := by
  let R := ((special Y).filter (fun e => e.2^2≤X/(e.1*e.2))).filter (fun e => 23<e.2)
  let old (p : ℕ) := ((range W).filter (fun i => 0<b*W+i ∧
      (descendingPrimes (p-1)).all (fun q => decide (¬q ∣ b*W+i)))).card
  have idx : R=S := by ext e; simp only [R,S,hardEdges,mem_filter,not_lt]
  change (∑ p ∈ R.image (fun e => e.2), (old p : ℤ) *
    (∑ e ∈ R.filter (fun e => e.2=p ∧ b<(X/(e.1*e.2))/W), -moebius e.1)) = _
  rw [idx, FullLookup.row_eq_cells (fun h => FullLookup.roster_entry h) FullLookup.coeff_of_tables]
  apply sum_congr rfl
  intro p hp
  obtain ⟨e,he,rfl⟩ := mem_image.mp hp
  exact congrArg (fun v : ℕ => (v : ℤ)*weight e.2 b) (original_count _ _ (mem_filter.mp he).2)
end Astra247824.SquareBand


namespace Astra247824.SquareBand
open Finset ArithmeticFunction
def originalRow (b : ℕ) : ℤ :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun b : ℕ => ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1)
  f b

def originalPrefix (n : ℕ) : ℤ := ∑ b ∈ range n, originalRow b

private theorem originalPrefix_eq [FullLookup.CheckedWeights] (n : ℕ) :
    originalPrefix n = FullLookup.rowPrefix n :=
  sum_congr rfl (fun b _ => original_row_value b)

theorem original_interval [FullLookup.CheckedWeights] (lo hi : ℕ) (v : ℤ)
    (h : FullLookup.rowPrefix hi - FullLookup.rowPrefix lo = v) :
    originalPrefix hi - originalPrefix lo = v :=
  (congrArg₂ (fun x y : ℤ => x-y) (originalPrefix_eq hi) (originalPrefix_eq lo)).trans h
end Astra247824.SquareBand

namespace Astra247824.FullLookup
private def w1024 : ℕ := 0x89b3220622e958ff28d93e4dae3f1b1883
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1024 : PLift (tilesMatch 4 34 4 1024 w1024 = true) := ⟨by decide +kernel⟩
private theorem tile1024 : rowPrefix 1088 - rowPrefix 1024 = 37762155512 :=
  checked_tiles 4 34 4 1024 w1024 c1024.down
private def w1088 : ℕ := 0x824b3479610081fbc85d005eae1ee834d0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1088 : PLift (tilesMatch 4 34 4 1088 w1088 = true) := ⟨by decide +kernel⟩
private theorem tile1088 : rowPrefix 1152 - rowPrefix 1088 = 35691249180 :=
  checked_tiles 4 34 4 1088 w1088 c1088.down
private def w1152 : ℕ := 0x7b7e639c5f48398887ed2fc986023899de
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1152 : PLift (tilesMatch 4 34 4 1152 w1152 = true) := ⟨by decide +kernel⟩
private theorem tile1152 : rowPrefix 1216 - rowPrefix 1152 = 33822978872 :=
  checked_tiles 4 34 4 1152 w1152 c1152.down
private def w1216 : ℕ := 0xeaf1650376f4c78b3c39f34c3e78b6c94
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1216 : PLift (tilesMatch 4 33 4 1216 w1216 = true) := ⟨by decide +kernel⟩
private theorem tile1216 : rowPrefix 1280 - rowPrefix 1216 = 32129478439 :=
  checked_tiles 4 33 4 1216 w1216 c1216.down
private def w1280 : ℕ := 0xdfb60d5a71437f787950b1465d006ef93
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1280 : PLift (tilesMatch 4 33 4 1280 w1280 = true) := ⟨by decide +kernel⟩
private theorem tile1280 : rowPrefix 1344 - rowPrefix 1280 = 30585295450 :=
  checked_tiles 4 33 4 1280 w1280 c1280.down
private def w1344 : ℕ := 0xd59dc9066c2000ed36a838de7ba3ba80a
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1344 : PLift (tilesMatch 4 33 4 1344 w1344 = true) := ⟨by decide +kernel⟩
private theorem tile1344 : rowPrefix 1408 - rowPrefix 1344 = 29179315389 :=
  checked_tiles 4 33 4 1344 w1344 c1344.down
private def w1408 : ℕ := 0xcc8e9d96675f625b3440a97b1a698d065
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1408 : PLift (tilesMatch 4 33 4 1408 w1408 = true) := ⟨by decide +kernel⟩
private theorem tile1408 : rowPrefix 1472 - rowPrefix 1408 = 27904237781 :=
  checked_tiles 4 33 4 1408 w1408 c1408.down
private def w1472 : ℕ := 0xc40c718562fedad4f2099fd7794c7a863
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1472 : PLift (tilesMatch 4 33 4 1472 w1472 = true) := ⟨by decide +kernel⟩
private theorem tile1472 : rowPrefix 1536 - rowPrefix 1472 = 26728789371 :=
  checked_tiles 4 33 4 1472 w1472 c1472.down
private def w1536 : ℕ := 0xbc4a65f0df054ac170034b81b841671f7
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1536 : PLift (tilesMatch 4 33 4 1536 w1536 = true) := ⟨by decide +kernel⟩
private theorem tile1536 : rowPrefix 1600 - rowPrefix 1536 = 25649923306 :=
  checked_tiles 4 33 4 1536 w1536 c1536.down
private def w1600 : ℕ := 0xb530e8abdb779faf2e22ded6574ce6087
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1600 : PLift (tilesMatch 4 33 4 1600 w1600 = true) := ⟨by decide +kernel⟩
private theorem tile1600 : rowPrefix 1664 - rowPrefix 1600 = 24664975180 :=
  checked_tiles 4 33 4 1600 w1600 c1600.down
private def w1664 : ℕ := 0xae3cbf6257fbcc97ac6510e0566dc9c3f
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1664 : PLift (tilesMatch 4 33 4 1664 w1664 = true) := ⟨by decide +kernel⟩
private theorem tile1664 : rowPrefix 1728 - rowPrefix 1664 = 23730181219 :=
  checked_tiles 4 33 4 1664 w1664 c1664.down
private def w1728 : ℕ := 0xa8211752d4d19ca1eac53c66d59512f9e
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1728 : PLift (tilesMatch 4 33 4 1728 w1728 = true) := ⟨by decide +kernel⟩
private theorem tile1728 : rowPrefix 1792 - rowPrefix 1728 = 22867588096 :=
  checked_tiles 4 33 4 1728 w1728 c1728.down
private def w1792 : ℕ := 0xa24673c351d14acb29489ca154d314009
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1792 : PLift (tilesMatch 4 33 4 1792 w1792 = true) := ⟨by decide +kernel⟩
private theorem tile1792 : rowPrefix 1856 - rowPrefix 1792 = 22066771909 :=
  checked_tiles 4 33 4 1792 w1792 c1792.down
private def w1856 : ℕ := 0x9cc960b44f0d1dd427dd4481941945920
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1856 : PLift (tilesMatch 4 33 4 1856 w1856 = true) := ⟨by decide +kernel⟩
private theorem tile1856 : rowPrefix 1920 - rowPrefix 1856 = 21311632868 :=
  checked_tiles 4 33 4 1856 w1856 c1856.down
private def w1920 : ℕ := 0x9789869f4c6e10c1e68a273cd36d4b359
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1920 : PLift (tilesMatch 4 33 4 1920 w1920 = true) := ⟨by decide +kernel⟩
private theorem tile1920 : rowPrefix 1984 - rowPrefix 1920 = 20601453956 :=
  checked_tiles 4 33 4 1920 w1920 c1920.down
private def w1984 : ℕ := 0x92a98347c9e36618253a20ac72c78441a
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c1984 : PLift (tilesMatch 4 33 4 1984 w1984 = true) := ⟨by decide +kernel⟩
private theorem tile1984 : rowPrefix 2048 - rowPrefix 1984 = 19917301868 :=
  checked_tiles 4 33 4 1984 w1984 c1984.down
private def w2048 : ℕ := 0x8e254f59c79bb3e62416ababd23027002
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2048 : PLift (tilesMatch 4 33 4 2048 w2048 = true) := ⟨by decide +kernel⟩
private theorem tile2048 : rowPrefix 2112 - rowPrefix 2048 = 19301219243 :=
  checked_tiles 4 33 4 2048 w2048 c2048.down
private def w2112 : ℕ := 0x89f5489bc579a10722fdbfd6719f94acb
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2112 : PLift (tilesMatch 4 33 4 2112 w2112 = true) := ⟨by decide +kernel⟩
private theorem tile2112 : rowPrefix 2176 - rowPrefix 2112 = 18718678737 :=
  checked_tiles 4 33 4 2112 w2112 c2112.down
private def w2176 : ℕ := 0x85d08b26c36aca0021fa4d29f11e2a7bb
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2176 : PLift (tilesMatch 4 33 4 2176 w2176 = true) := ⟨by decide +kernel⟩
private theorem tile2176 : rowPrefix 2240 - rowPrefix 2176 = 18169810775 :=
  checked_tiles 4 33 4 2176 w2176 c2176.down
private def w2240 : ℕ := 0x820009a4c174ce0420f73e02b0990902d
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2240 : PLift (tilesMatch 4 33 4 2240 w2240 = true) := ⟨by decide +kernel⟩
private theorem tile2240 : rowPrefix 2304 - rowPrefix 2240 = 17634806683 :=
  checked_tiles 4 33 4 2240 w2240 c2240.down
private def w2304 : ℕ := 0x7e51ed1d3f9a0443e0087b7b1022bb92e
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2304 : PLift (tilesMatch 4 33 4 2304 w2304 = true) := ⟨by decide +kernel⟩
private theorem tile2304 : rowPrefix 2368 - rowPrefix 2304 = 17137631311 :=
  checked_tiles 4 33 4 2304 w2304 c2304.down
private def w2368 : ℕ := 0xf5d9d6e2f77c531ef930690cfad19178
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2368 : PLift (tilesMatch 4 32 4 2368 w2368 = true) := ⟨by decide +kernel⟩
private theorem tile2368 : rowPrefix 2432 - rowPrefix 2368 = 16665552004 :=
  checked_tiles 4 32 4 2368 w2368 c2368.down
private def w2432 : ℕ := 0xef228c9ef0d5d9a3f2799b7bf421e21b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2432 : PLift (tilesMatch 4 32 4 2432 w2432 = true) := ⟨by decide +kernel⟩
private theorem tile2432 : rowPrefix 2496 - rowPrefix 2432 = 16216482775 :=
  checked_tiles 4 32 4 2432 w2432 c2432.down
private def w2496 : ℕ := 0xe9178c28eaa2b34fec120c2deda01f46
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2496 : PLift (tilesMatch 4 32 4 2496 w2496 = true) := ⟨by decide +kernel⟩
private theorem tile2496 : rowPrefix 2560 - rowPrefix 2496 = 15794465514 :=
  checked_tiles 4 32 4 2496 w2496 c2496.down
private def w2560 : ℕ := 0xe30bd200e4785614e5f145a8e799cf0f
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2560 : PLift (tilesMatch 4 32 4 2560 w2560 = true) := ⟨by decide +kernel⟩
private theorem tile2560 : rowPrefix 2624 - rowPrefix 2560 = 15385705675 :=
  checked_tiles 4 32 4 2560 w2560 c2560.down
private def w2624 : ℕ := 0xdd9bc0bbdf075a2fe0627ef8e1987ce2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2624 : PLift (tilesMatch 4 32 4 2624 w2624 = true) := ⟨by decide +kernel⟩
private theorem tile2624 : rowPrefix 2688 - rowPrefix 2624 = 15009191620 :=
  checked_tiles 4 32 4 2624 w2624 c2624.down
private def w2688 : ℕ := 0xd809f9e9d9476ccedac68250dc344693
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2688 : PLift (tilesMatch 4 32 4 2688 w2688 = true) := ⟨by decide +kernel⟩
private theorem tile2688 : rowPrefix 2752 - rowPrefix 2688 = 14634725274 :=
  checked_tiles 4 32 4 2688 w2688 c2688.down
private def w2752 : ℕ := 0xd2b06279d3fa2f70d5548212d66d295e
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2752 : PLift (tilesMatch 4 32 4 2752 w2752 = true) := ⟨by decide +kernel⟩
private theorem tile2752 : rowPrefix 2816 - rowPrefix 2752 = 14267727193 :=
  checked_tiles 4 32 4 2752 w2752 c2752.down
private def w2816 : ℕ := 0xcdb0d506cedcb2ead024ac6bd1699749
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2816 : PLift (tilesMatch 4 32 4 2816 w2816 = true) := ⟨by decide +kernel⟩
private theorem tile2816 : rowPrefix 2880 - rowPrefix 2816 = 13926910884 :=
  checked_tiles 4 32 4 2816 w2816 c2816.down
private def w2880 : ℕ := 0xc91affc4ca62ce32cba76ac4cca874dc
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2880 : PLift (tilesMatch 4 32 4 2880 w2880 = true) := ⟨by decide +kernel⟩
private theorem tile2880 : rowPrefix 2944 - rowPrefix 2880 = 13619801494 :=
  checked_tiles 4 32 4 2880 w2880 c2880.down
private def w2944 : ℕ := 0xc49ffd8ec5c0c6edc6d59389c7fcc526
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c2944 : PLift (tilesMatch 4 32 4 2944 w2944 = true) := ⟨by decide +kernel⟩
private theorem tile2944 : rowPrefix 3008 - rowPrefix 2944 = 13307682090 :=
  checked_tiles 4 32 4 2944 w2944 c2944.down
private def w3008 : ℕ := 0xc05b19c2c156f553c265afa6c372b0c9
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3008 : PLift (tilesMatch 4 32 4 3008 w3008 = true) := ⟨by decide +kernel⟩
private theorem tile3008 : rowPrefix 3072 - rowPrefix 3008 = 13011414916 :=
  checked_tiles 4 32 4 3008 w3008 c3008.down
private def w3072 : ℕ := 0xbbf8ee8bbcefd205be283566bf332097
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3072 : PLift (tilesMatch 4 32 4 3072 w3072 = true) := ⟨by decide +kernel⟩
private theorem tile3072 : rowPrefix 3136 - rowPrefix 3072 = 12721591949 :=
  checked_tiles 4 32 4 3072 w3072 c3072.down
private def w3136 : ℕ := 0xb7fdc3c0b8ed38d3b9d6ff2fbae4daae
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3136 : PLift (tilesMatch 4 32 4 3136 w3136 = true) := ⟨by decide +kernel⟩
private theorem tile3136 : rowPrefix 3200 - rowPrefix 3136 = 12442850928 :=
  checked_tiles 4 32 4 3136 w3136 c3136.down
private def w3200 : ℕ := 0xb4146b6ab4f220feb5ed3066b705316f
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3200 : PLift (tilesMatch 4 32 4 3200 w3200 = true) := ⟨by decide +kernel⟩
private theorem tile3200 : rowPrefix 3264 - rowPrefix 3200 = 12179795517 :=
  checked_tiles 4 32 4 3200 w3200 c3200.down
private def w3264 : ℕ := 0xb03efcfab1259ee9b21ccddcb318fa9b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3264 : PLift (tilesMatch 4 32 4 3264 w3264 = true) := ⟨by decide +kernel⟩
private theorem tile3264 : rowPrefix 3328 - rowPrefix 3264 = 11921941594 :=
  checked_tiles 4 32 4 3264 w3264 c3264.down
private def w3328 : ℕ := 0xac90181bad75fd46ae6c73f8af5ba3a3
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3328 : PLift (tilesMatch 4 32 4 3328 w3328 = true) := ⟨by decide +kernel⟩
private theorem tile3328 : rowPrefix 3392 - rowPrefix 3328 = 11673677052 :=
  checked_tiles 4 32 4 3328 w3328 c3328.down
private def w3392 : ℕ := 0xa90abac6a9f4bcc5aac6e9beab9e4da6
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3392 : PLift (tilesMatch 4 32 4 3392 w3392 = true) := ⟨by decide +kernel⟩
private theorem tile3392 : rowPrefix 3456 - rowPrefix 3392 = 11431882479 :=
  checked_tiles 4 32 4 3392 w3392 c3392.down
private def w3456 : ℕ := 0xa575acb7a66c0351a742804ca81afa99
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3456 : PLift (tilesMatch 4 32 4 3456 w3456 = true) := ⟨by decide +kernel⟩
private theorem tile3456 : rowPrefix 3520 - rowPrefix 3456 = 11194542829 :=
  checked_tiles 4 32 4 3456 w3456 c3456.down
private def w3520 : ℕ := 0xa24c19f0a321e7e1a3e6cf73a4a32f54
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3520 : PLift (tilesMatch 4 32 4 3520 w3520 = true) := ⟨by decide +kernel⟩
private theorem tile3520 : rowPrefix 3584 - rowPrefix 3520 = 10971775128 :=
  checked_tiles 4 32 4 3520 w3520 c3520.down
private def w3584 : ℕ := 0x9f38c41e9ff98f84a0cfb23da1828f74
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3584 : PLift (tilesMatch 4 32 4 3584 w3584 = true) := ⟨by decide +kernel⟩
private theorem tile3584 : rowPrefix 3648 - rowPrefix 3584 = 10762884435 :=
  checked_tiles 4 32 4 3584 w3584 c3584.down
private def w3648 : ℕ := 0x9c4663259cf5cf839dce95e19e931ee1
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3648 : PLift (tilesMatch 4 32 4 3648 w3648 = true) := ⟨by decide +kernel⟩
private theorem tile3648 : rowPrefix 3712 - rowPrefix 3648 = 10563217258 :=
  checked_tiles 4 32 4 3648 w3648 c3648.down
private def w3712 : ℕ := 0x995e38e39a16a9899ad9d31a9b9839d0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3712 : PLift (tilesMatch 4 32 4 3712 w3712 = true) := ⟨by decide +kernel⟩
private theorem tile3712 : rowPrefix 3776 - rowPrefix 3712 = 10366676822 :=
  checked_tiles 4 32 4 3712 w3712 c3712.down
private def w3776 : ℕ := 0x9695506197483e1097ee79b498aab7f5
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3776 : PLift (tilesMatch 4 32 4 3776 w3776 = true) := ⟨by decide +kernel⟩
private theorem tile3776 : rowPrefix 3840 - rowPrefix 3776 = 10174775322 :=
  checked_tiles 4 32 4 3776 w3776 c3776.down
private def w3840 : ℕ := 0x93b4e153947979379529f3ba95eaed85
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3840 : PLift (tilesMatch 4 32 4 3840 w3840 = true) := ⟨by decide +kernel⟩
private theorem tile3840 : rowPrefix 3904 - rowPrefix 3840 = 9986849737 :=
  checked_tiles 4 32 4 3840 w3840 c3840.down
private def w3904 : ℕ := 0x914b4eec91f88a1a9285a91b93196237
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3904 : PLift (tilesMatch 4 32 4 3904 w3904 = true) := ⟨by decide +kernel⟩
private theorem tile3904 : rowPrefix 3968 - rowPrefix 3904 = 9812763736 :=
  checked_tiles 4 32 4 3904 w3904 c3904.down
private def w3968 : ℕ := 0x8ebdf6478f755b18901a53f490b4a080
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c3968 : PLift (tilesMatch 4 32 4 3968 w3968 = true) := ⟨by decide +kernel⟩
private theorem tile3968 : rowPrefix 4032 - rowPrefix 3968 = 9647048147 :=
  checked_tiles 4 32 4 3968 w3968 c3968.down
private def w4032 : ℕ := 0x8c4b22ef8cc093f28d6e74218e17e7c1
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4032 : PLift (tilesMatch 4 32 4 4032 w4032 = true) := ⟨by decide +kernel⟩
private theorem tile4032 : rowPrefix 4096 - rowPrefix 4032 = 9471922883 :=
  checked_tiles 4 32 4 4032 w4032 c4032.down
private def w4096 : ℕ := 0x87923bec880c449988b6bf8e8940228f89f9a3778a77bc4c8b1d7bfc8baefda8
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4096 : PLift (tilesMatch 4 32 8 4096 w4096 = true) := ⟨by decide +kernel⟩
private theorem tile4096 : rowPrefix 4224 - rowPrefix 4096 = 18468781065 :=
  checked_tiles 4 32 8 4096 w4096 c4096.down
private def w4224 : ℕ := 0x82e4850b8383fb4a840824308482839684fbf63485bb8ef98659ce1286fe903b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4224 : PLift (tilesMatch 4 32 8 4224 w4224 = true) := ⟨by decide +kernel⟩
private theorem tile4224 : rowPrefix 4352 - rowPrefix 4224 = 17834380181 :=
  checked_tiles 4 32 8 4224 w4224 c4224.down
private def w4352 : ℕ := 0x7ea10d407f29bf3a7fb1d6b28018b64e80aa88a9813b595581bec4ec82543d60
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4352 : PLift (tilesMatch 4 32 8 4352 w4352 = true) := ⟨by decide +kernel⟩
private theorem tile4352 : rowPrefix 4480 - rowPrefix 4352 = 17239522756 :=
  checked_tiles 4 32 8 4352 w4352 c4352.down
private def w4480 : ℕ := 0xf50162d9ebfba26bdb9cf8afc1856a8f9221b45f473fbdbec6bc767e1d96b2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4480 : PLift (tilesMatch 4 31 8 4480 w4480 = true) := ⟨by decide +kernel⟩
private theorem tile4480 : rowPrefix 4608 - rowPrefix 4480 = 16683150329 :=
  checked_tiles 4 31 8 4480 w4480 c4480.down
private def w4608 : ℕ := 0xed7be225dce1a4ebbd378b37821fafdf11e9bc5e3f17a1bcbfae8b79ff957b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4608 : PLift (tilesMatch 4 31 8 4608 w4608 = true) := ⟨by decide +kernel⟩
private theorem tile4608 : rowPrefix 4736 - rowPrefix 4608 = 16152913320 :=
  checked_tiles 4 31 8 4608 w4608 c4608.down
private def w4736 : ℕ := 0xe61d60e5ce113b27a03b135f4675d0ae9cb34a3d57ab4bfaf1d337f657b433
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4736 : PLift (tilesMatch 4 31 8 4736 w4736 = true) := ⟨by decide +kernel⟩
private theorem tile4736 : rowPrefix 4864 - rowPrefix 4736 = 15661621458 :=
  checked_tiles 4 31 8 4736 w4736 c4736.down
private def w4864 : ℕ := 0xdf05459dbfdf4de783527ec70d62ef9e2a1f48dc712f18f915ac70729eb0e8
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4864 : PLift (tilesMatch 4 31 8 4864 w4864 = true) := ⟨by decide +kernel⟩
private theorem tile4864 : rowPrefix 4992 - rowPrefix 4864 = 15176742281 :=
  checked_tiles 4 31 8 4864 w4864 c4864.down
private def w4992 : ℕ := 0xd8d13cddb3233fe7692d6366d942373dbd760f3b94aa87f756440e6f1ac278
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def c4992 : PLift (tilesMatch 4 31 8 4992 w4992 = true) := ⟨by decide +kernel⟩
private theorem tile4992 : rowPrefix 5120 - rowPrefix 4992 = 14729405298 :=
  checked_tiles 4 31 8 4992 w4992 c4992.down
set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem interval_values : rowPrefix 5120 - rowPrefix 1024 = 994685847088 :=
  (append_tile_sum (append_tile_sum (append_tile_sum (append_tile_sum (append_tile_sum tile1024 (append_tile_sum tile1088 tile1152)) (append_tile_sum (append_tile_sum tile1216 tile1280) (append_tile_sum tile1344 tile1408))) (append_tile_sum (append_tile_sum tile1472 (append_tile_sum tile1536 tile1600)) (append_tile_sum (append_tile_sum tile1664 tile1728) (append_tile_sum tile1792 tile1856)))) (append_tile_sum (append_tile_sum (append_tile_sum tile1920 (append_tile_sum tile1984 tile2048)) (append_tile_sum (append_tile_sum tile2112 tile2176) (append_tile_sum tile2240 tile2304))) (append_tile_sum (append_tile_sum tile2368 (append_tile_sum tile2432 tile2496)) (append_tile_sum (append_tile_sum tile2560 tile2624) (append_tile_sum tile2688 tile2752))))) (append_tile_sum (append_tile_sum (append_tile_sum (append_tile_sum tile2816 (append_tile_sum tile2880 tile2944)) (append_tile_sum (append_tile_sum tile3008 tile3072) (append_tile_sum tile3136 tile3200))) (append_tile_sum (append_tile_sum tile3264 (append_tile_sum tile3328 tile3392)) (append_tile_sum (append_tile_sum tile3456 tile3520) (append_tile_sum tile3584 tile3648)))) (append_tile_sum (append_tile_sum (append_tile_sum tile3712 (append_tile_sum tile3776 tile3840)) (append_tile_sum (append_tile_sum tile3904 tile3968) (append_tile_sum tile4032 tile4096))) (append_tile_sum (append_tile_sum tile4224 (append_tile_sum tile4352 tile4480)) (append_tile_sum (append_tile_sum tile4608 tile4736) (append_tile_sum tile4864 tile4992))))))
end Astra247824.FullLookup


open Astra247824 in
theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H3_R1.H2 :=
  @SquareBand.original_interval FullLookup.direct_weights 1024 5120 994685847088 FullLookup.interval_values
