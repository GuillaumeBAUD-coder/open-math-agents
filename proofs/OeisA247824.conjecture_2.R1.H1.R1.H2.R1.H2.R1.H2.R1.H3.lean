import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Count
import Mathlib.Tactic

/- Endpoint sieve for the finite Legendre sum. The signed decomposition uses the parent by @physbuzz, credited there to Daniel Veljjanoski and @rleshner (PR #9315). The segmented masks, denominator tables and batch certificates are from @Medrov. -/

namespace Astra247824
open Finset
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

def hardEdges (x y : ℕ) : Finset Edge :=
  (special y).filter (fun e => ¬ x/(e.1*e.2) < e.2^2)
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

theorem indexed_hard_block {x y p width b d : ℕ} (pp : p.Prime) (ww : 0<width) :
    ((⟨d,p⟩ : Edge) ∈ hardEdges x y ∧ x/(d*p)/width=b) ↔
      Squarefree d ∧ p < d.minFac ∧ max (max p (y/p)) (x/(p*((b+1)*width))) < d ∧
        d ≤ (if b=0 then min y (x/p^3) else min (min y (x/p^3)) (x/(p*(b*width)))) := by
  rw [hard_denominator_iff pp]
  constructor
  · rintro ⟨⟨sf,fac,lower,upper⟩,atBlock⟩
    have dpos := pp.pos.trans (max_lt_iff.mp lower).1
    have next : x/(p*((b+1)*width)) < d := lt_of_not_ge (fun h =>
      (by omega : ¬ b < x/(d*p)/width) ((late_iff (x:=x) dpos pp.pos ww).mpr h))
    refine ⟨sf,fac,max_lt lower next,?_⟩
    cases b with
    | zero => exact upper
    | succ k =>
      have prev := (late_iff (x:=x) (b:=k) dpos pp.pos ww).mp (by omega)
      exact le_min upper prev
  · rintro ⟨sf,fac,low,high⟩
    obtain ⟨lower,caplast⟩ := max_lt_iff.mp low
    have dpos := pp.pos.trans (max_lt_iff.mp lower).1
    have cap : x/(d*p)/width≤b := not_lt.mp (fun h => (not_le.mpr caplast) ((late_iff (x:=x) dpos pp.pos ww).mp h))
    cases b with
    | zero => exact ⟨⟨sf,fac,lower,high⟩,Nat.eq_zero_of_le_zero cap⟩
    | succ k =>
      have bounds : d ≤ min (min y (x/p^3)) (x/(p*((k+1)*width))) := high
      obtain ⟨upper,prev⟩ := le_min_iff.mp bounds
      have floor := (late_iff (x:=x) (b:=k) dpos pp.pos ww).mpr prev
      exact ⟨⟨sf,fac,lower,upper⟩,by omega⟩

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


namespace Astra247824.HardTail
open Finset Leaves ArithmeticFunction
abbrev X : ℕ := 81744924555066

abbrev Y : ℕ := 43399

abbrev W : ℕ := 65536

def tail (p t : ℕ) : ℕ :=
  let lo := (t/W)*W
  ((range (t%W+1)).filter (fun i => 0<lo+i ∧
    (descendingPrimes (p-1)).all (fun q => decide (¬q ∣ lo+i)))).card

theorem tail_eq_segment (p t : ℕ) (large : 23<p) :
    tail p t = segmentCount (descendingPrimes (p-1)) ((t/W)*W) (t%W+1) := by
  let ps := descendingPrimes (p-1)
  let lo := t/W*W
  have two : 2 ∈ ps := mem_descending.mpr (Nat.mem_primesLE.mpr ⟨by omega,by decide⟩)
  change ((range (t%W+1)).filter (fun i => 0<lo+i ∧ ps.all (fun q => decide (¬q ∣ lo+i)))).card =
    segmentCount ps lo (t%W+1)
  unfold segmentCount
  congr 1
  ext i
  simp only [mem_filter,List.all_eq_true,decide_eq_true_eq]
  constructor
  · exact fun ⟨hi,_,clean⟩ => ⟨hi,clean⟩
  · rintro ⟨hi,clean⟩
    refine ⟨hi,?_,clean⟩
    by_contra! out
    have zero : lo+i=0 := by omega
    exact (clean 2 two) (by rw [zero]; exact dvd_zero 2)

abbrev S := (hardEdges X Y).filter (fun e => 23<e.2)

def term (e : Edge) : ℤ := -moebius e.1 * (tail e.2 (X/(e.1*e.2)) : ℤ)

theorem original_iff_sum :
    OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H2 ↔
      (∑ e ∈ S, term e)=3098980124 := by
  let R := ((special Y).filter (fun e => e.2^2≤X/(e.1*e.2))).filter (fun e => 23<e.2)
  have idx : R=S := by ext e; simp only [R,S,hardEdges,mem_filter,not_lt]
  change (∑ e ∈ R, term e) = 3098980124 ↔ _
  rw [idx]
end Astra247824.HardTail


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

/- Prefix counts from a single 32-bit-field summary of each hard sieve segment. -/

namespace Astra247824
open Finset
/- Counts of consecutive source bits in radix-2^s fields with no inter-field carries. -/
def packedClasses (s k n : ℕ) : ℕ :=
  ∑ r ∈ range s, ((n >>> r) &&& ((2^(s*k)-1)/(2^s-1)))

private def classCount (s n j : ℕ) := ((range s).filter (fun r => n.testBit (s*j+r))).card

private theorem class_word (s k n r : ℕ) (hs : 0<s) :
    ((n >>> r) &&& ((2^(s*k)-1)/(2^s-1))) =
      ∑ j ∈ range k, if n.testBit (s*j+r) then 2^(s*j) else 0 := by
  let W := ((n >>> r) &&& ((2^(s*k)-1)/(2^s-1)))
  let S := (range k).filter (fun j => n.testBit (s*j+r))
  have support : W.bitIndices.toFinset = S.image (fun j => s*j) := by
    ext i
    simp only [List.mem_toFinset, Nat.mem_bitIndices,mem_image,W,Nat.testBit_and,
      Nat.testBit_shiftRight,← multiplesMask_fast hs,multiplesMask_spec hs,Bool.and_eq_true,
      S,mem_filter,mem_range]
    constructor
    · rintro ⟨h,j,hj,rfl⟩
      exact ⟨j,⟨hj,by simpa [Nat.add_comm] using h⟩,rfl⟩
    · rintro ⟨j,⟨hj,h⟩,rfl⟩
      exact ⟨by simpa [Nat.add_comm] using h,j,hj,rfl⟩
  change W = _
  rw [← Finset.sum_toFinset_bitIndices_two_pow W, support, Finset.sum_image]
  · exact sum_filter ..
  · exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hs h

theorem packedClasses_eq (s k n : ℕ) (hs : 0<s) :
    packedClasses s k n = ∑ j ∈ range k, classCount s n j * (2^s)^j := by
  unfold packedClasses
  have expanded : (∑ r ∈ range s, ((n >>> r) &&& ((2^(s*k)-1)/(2^s-1)))) =
      ∑ r ∈ range s, ∑ j ∈ range k, if n.testBit (s*j+r) then 2^(s*j) else 0 :=
    sum_congr rfl (fun r _ => class_word s k n r hs)
  rw [expanded,sum_comm]
  apply sum_congr rfl
  intro j _
  have eq := sum_mul (s:=range s) (f:=fun r => if n.testBit (s*j+r) then (1:ℕ) else 0) ((2^s)^j)
  simpa only [pow_mul,ite_mul,one_mul,zero_mul,sum_boole,Nat.cast_id,classCount] using eq.symm

private theorem digits_lt {B : ℕ} (_pos : 0<B) (f : ℕ → ℕ) (small : ∀ j, f j < B) (k : ℕ) :
    ∑ j ∈ range k, f j*B^j < B^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    calc
      _ < B^k + f k*B^k := Nat.add_lt_add_right ih _
      _ = (f k+1)*B^k := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
      _ ≤ _ := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (B^k) (small k)

private theorem lower_digits {B k q : ℕ} (pos : 0<B) (hq : q≤k) (f : ℕ → ℕ)
    (small : ∀ j, f j < B) :
    (∑ j ∈ range k, f j*B^j) % B^q = ∑ j ∈ range q, f j*B^j := by
  conv_lhs => rw [← Nat.add_sub_of_le hq, sum_range_add]
  have divs : B^q ∣ ∑ i ∈ range (k-q), f (q+i)*B^(q+i) := by
    apply Finset.dvd_sum
    intro i _
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ (Nat.le_add_right _ _)) _
  have z := Nat.add_mod (∑ j ∈ range q, f j*B^j)
    (∑ i ∈ range (k-q), f (q+i)*B^(q+i)) (B^q)
  rw [Nat.mod_eq_zero_of_dvd divs, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (digits_lt pos f small q)] at z
  exact z

private theorem count_classes (s n q : ℕ) :
    ∑ j ∈ range q, classCount s n j =
      ((range (s*q)).filter (fun i => n.testBit i)).card := by
  have h (m : ℕ) : ∑ j ∈ range m, classCount s n j =
      ∑ i ∈ range (s*m), if n.testBit i then 1 else 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih, Nat.mul_succ, sum_range_add]
      simp only [classCount,sum_boole,Nat.cast_id]
  simpa only [sum_boole,Nat.cast_id] using h q

/- Full digital rank below a multiple of the field width, from a single packed word. -/
theorem packedClasses_prefix {s k q n : ℕ} (hs : 0<s) (hq : q≤k) (room : s*k < 2^s-1) :
    (packedClasses s k n % 2^(s*q)) % (2^s-1) =
      ((range (s*q)).filter (fun i => n.testBit i)).card := by
  let B := 2^s
  have positive : 0<B := Nat.two_pow_pos s
  have small (j : ℕ) : classCount s n j < B :=
    (card_filter_le ..).trans_lt (by simpa only [card_range,B] using (Nat.lt_two_pow_self (n:=s)))
  rw [packedClasses_eq _ _ _ hs,pow_mul,lower_digits positive hq _ small]
  have one : 1<B := Nat.one_lt_two_pow (by omega)
  have radix : B ≡ 1 [MOD B-1] := by
    change B%(B-1) = 1%(B-1)
    conv_lhs => arg 1; rw [show B=1+(B-1) by omega]
    exact Nat.add_mod_right _ _
  have same : (∑ j ∈ range q, classCount s n j * B^j) ≡
      ∑ j ∈ range q, classCount s n j [MOD B-1] := by
    apply Nat.ModEq.sum
    intro j _
    simpa only [one_pow,Nat.mul_one] using (radix.pow j).mul_left (classCount s n j)
  have bound : ((range (s*q)).filter (fun i => n.testBit i)).card < B-1 := by
    apply (card_filter_le ..).trans_lt
    rw [card_range]
    exact (Nat.mul_le_mul_left _ hq).trans_lt room
  change _ % (B-1) = _ % (B-1) at same
  rw [count_classes,Nat.mod_eq_of_lt bound] at same
  exact same

/- Look up an inclusive-prefix length in a 65,536-bit block, retaining only a final partial field. -/
def packedRank (word packed length : ℕ) : ℕ :=
  let start := 32*(length/32)
  (packed % 2^start) % 0xffffffff +
    GlobalRank.pop64 ((word >>> start) % 2^(length%32))

private theorem bit_count_add (word a b : ℕ) :
    ((range (a+b)).filter (fun i => word.testBit i)).card =
      ((range a).filter (fun i => word.testBit i)).card +
      ((range b).filter (fun i => word.testBit (a+i))).card := by
  have eq := sum_range_add (fun i => if word.testBit i then (1:ℕ) else 0) a b
  simpa only [sum_boole,Nat.cast_id] using eq

private theorem short_tail {word a b : ℕ} (h : b≤64) :
    GlobalRank.pop64 ((word >>> a)%2^b) = ((range b).filter (fun i => word.testBit (a+i))).card := by
  have small : (word >>> a)%2^b < 2^64 :=
    (Nat.mod_lt _ (Nat.two_pow_pos b)).trans_le (Nat.pow_le_pow_right (by decide) h)
  rw [GlobalRank.pop64_spec _ small]
  congr 1
  ext i
  simp only [mem_filter,mem_range,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨_, hr, flag⟩
    exact ⟨hr, by simpa only [Nat.add_comm] using flag⟩
  · rintro ⟨hr, flag⟩
    exact ⟨hr.trans_le h, hr, by simpa only [Nat.add_comm] using flag⟩

/- Exact rank for every right endpoint of a packed segment. -/
theorem packedRank_spec {word length : ℕ} (bound : length≤65536) :
    packedRank word (packedClasses 32 2048 word) length =
      ((range length).filter (fun i => word.testBit i)).card := by
  have hq : length/32≤2048 := by omega
  have full := packedClasses_prefix (n:=word) (s:=32) (k:=2048) (q:=length/32)
    (by decide) hq (by decide)
  have tail := short_tail (word:=word) (a:=32*(length/32)) (b:=length%32) (by omega)
  have both := congrArg₂ Nat.add full tail
  have finish := (bit_count_add word (32*(length/32)) (length%32)).symm
  exact both.trans (finish.trans (congrArg
    (fun t => ((range t).filter (fun i => word.testBit i)).card) (Nat.div_add_mod _ _)))

/- Every prefix returned from a cached word equals its interval of the mathematical sieve. -/
theorem packedRank_segment {ps : List ℕ} {word lo length : ℕ} (bound : length ≤ 65536)
    (bits : ∀ i < 65536, word.testBit i = true ↔ ∀ p ∈ ps, ¬ p ∣ lo+i) :
    packedRank word (packedClasses 32 2048 word) length = segmentCount ps lo length := by
  rw [packedRank_spec bound]
  unfold segmentCount
  congr 1
  ext i
  simp only [mem_filter,mem_range]
  exact and_congr_right (fun hi => bits i (hi.trans_le bound))

end Astra247824

/- Cached geometric progressions for clearing prime multiples from 65,536-bit
segments. Every stored natural number is materialized and checked by the kernel. -/
namespace Astra247824.HardTail.Patterns

/- Retain every residue other than zero; the extra p bits allow all block phases. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
def keep (p : ℕ) := (2^(W+p)-1) ^^^ fixedPattern p W
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def shiftedKeep (p : ℕ) : ℕ :=
  ((1 <<< (W+p))-1) ^^^ (((1 <<< (p*(W/p+2)))-1)/((1 <<< p)-1))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem keep_shifted (p : ℕ) : keep p=shiftedKeep p := by
  simp only [keep,shiftedKeep,fixedPattern,Nat.one_shiftLeft]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private abbrev Certified (p : ℕ) := {m : ℕ // keep p = m}
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def atPrime (p expected : ℕ) (ready : Certified expected) : Certified p :=
  if eq : p=expected then ⟨ready.val, by simpa only [eq] using ready.property⟩
  else ⟨keep p,rfl⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2 : Certified 2 := ⟨_, (keep_shifted 2).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c3 : Certified 3 := ⟨_, (keep_shifted 3).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c5 : Certified 5 := ⟨_, (keep_shifted 5).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c7 : Certified 7 := ⟨_, (keep_shifted 7).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c11 : Certified 11 := ⟨_, (keep_shifted 11).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c13 : Certified 13 := ⟨_, (keep_shifted 13).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c17 : Certified 17 := ⟨_, (keep_shifted 17).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c19 : Certified 19 := ⟨_, (keep_shifted 19).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c23 : Certified 23 := ⟨_, (keep_shifted 23).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c29 : Certified 29 := ⟨_, (keep_shifted 29).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c31 : Certified 31 := ⟨_, (keep_shifted 31).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c37 : Certified 37 := ⟨_, (keep_shifted 37).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c41 : Certified 41 := ⟨_, (keep_shifted 41).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c43 : Certified 43 := ⟨_, (keep_shifted 43).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c47 : Certified 47 := ⟨_, (keep_shifted 47).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c53 : Certified 53 := ⟨_, (keep_shifted 53).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c59 : Certified 59 := ⟨_, (keep_shifted 59).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c61 : Certified 61 := ⟨_, (keep_shifted 61).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c67 : Certified 67 := ⟨_, (keep_shifted 67).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c71 : Certified 71 := ⟨_, (keep_shifted 71).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c73 : Certified 73 := ⟨_, (keep_shifted 73).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c79 : Certified 79 := ⟨_, (keep_shifted 79).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c83 : Certified 83 := ⟨_, (keep_shifted 83).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c89 : Certified 89 := ⟨_, (keep_shifted 89).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c97 : Certified 97 := ⟨_, (keep_shifted 97).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c101 : Certified 101 := ⟨_, (keep_shifted 101).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c103 : Certified 103 := ⟨_, (keep_shifted 103).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c107 : Certified 107 := ⟨_, (keep_shifted 107).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c109 : Certified 109 := ⟨_, (keep_shifted 109).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c113 : Certified 113 := ⟨_, (keep_shifted 113).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c127 : Certified 127 := ⟨_, (keep_shifted 127).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c131 : Certified 131 := ⟨_, (keep_shifted 131).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c137 : Certified 137 := ⟨_, (keep_shifted 137).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c139 : Certified 139 := ⟨_, (keep_shifted 139).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c149 : Certified 149 := ⟨_, (keep_shifted 149).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c151 : Certified 151 := ⟨_, (keep_shifted 151).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c157 : Certified 157 := ⟨_, (keep_shifted 157).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c163 : Certified 163 := ⟨_, (keep_shifted 163).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c167 : Certified 167 := ⟨_, (keep_shifted 167).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c173 : Certified 173 := ⟨_, (keep_shifted 173).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c179 : Certified 179 := ⟨_, (keep_shifted 179).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c181 : Certified 181 := ⟨_, (keep_shifted 181).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c191 : Certified 191 := ⟨_, (keep_shifted 191).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c193 : Certified 193 := ⟨_, (keep_shifted 193).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c197 : Certified 197 := ⟨_, (keep_shifted 197).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c199 : Certified 199 := ⟨_, (keep_shifted 199).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c211 : Certified 211 := ⟨_, (keep_shifted 211).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c223 : Certified 223 := ⟨_, (keep_shifted 223).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c227 : Certified 227 := ⟨_, (keep_shifted 227).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c229 : Certified 229 := ⟨_, (keep_shifted 229).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c233 : Certified 233 := ⟨_, (keep_shifted 233).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c239 : Certified 239 := ⟨_, (keep_shifted 239).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c241 : Certified 241 := ⟨_, (keep_shifted 241).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c251 : Certified 251 := ⟨_, (keep_shifted 251).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c257 : Certified 257 := ⟨_, (keep_shifted 257).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c263 : Certified 263 := ⟨_, (keep_shifted 263).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c269 : Certified 269 := ⟨_, (keep_shifted 269).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c271 : Certified 271 := ⟨_, (keep_shifted 271).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c277 : Certified 277 := ⟨_, (keep_shifted 277).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c281 : Certified 281 := ⟨_, (keep_shifted 281).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c283 : Certified 283 := ⟨_, (keep_shifted 283).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c293 : Certified 293 := ⟨_, (keep_shifted 293).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c307 : Certified 307 := ⟨_, (keep_shifted 307).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c311 : Certified 311 := ⟨_, (keep_shifted 311).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c313 : Certified 313 := ⟨_, (keep_shifted 313).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c317 : Certified 317 := ⟨_, (keep_shifted 317).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c331 : Certified 331 := ⟨_, (keep_shifted 331).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c337 : Certified 337 := ⟨_, (keep_shifted 337).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c347 : Certified 347 := ⟨_, (keep_shifted 347).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c349 : Certified 349 := ⟨_, (keep_shifted 349).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c353 : Certified 353 := ⟨_, (keep_shifted 353).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c359 : Certified 359 := ⟨_, (keep_shifted 359).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c367 : Certified 367 := ⟨_, (keep_shifted 367).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c373 : Certified 373 := ⟨_, (keep_shifted 373).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c379 : Certified 379 := ⟨_, (keep_shifted 379).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c383 : Certified 383 := ⟨_, (keep_shifted 383).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c389 : Certified 389 := ⟨_, (keep_shifted 389).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c397 : Certified 397 := ⟨_, (keep_shifted 397).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c401 : Certified 401 := ⟨_, (keep_shifted 401).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c409 : Certified 409 := ⟨_, (keep_shifted 409).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c419 : Certified 419 := ⟨_, (keep_shifted 419).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c421 : Certified 421 := ⟨_, (keep_shifted 421).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c431 : Certified 431 := ⟨_, (keep_shifted 431).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c433 : Certified 433 := ⟨_, (keep_shifted 433).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c439 : Certified 439 := ⟨_, (keep_shifted 439).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c443 : Certified 443 := ⟨_, (keep_shifted 443).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c449 : Certified 449 := ⟨_, (keep_shifted 449).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c457 : Certified 457 := ⟨_, (keep_shifted 457).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c461 : Certified 461 := ⟨_, (keep_shifted 461).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c463 : Certified 463 := ⟨_, (keep_shifted 463).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c467 : Certified 467 := ⟨_, (keep_shifted 467).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c479 : Certified 479 := ⟨_, (keep_shifted 479).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c487 : Certified 487 := ⟨_, (keep_shifted 487).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c491 : Certified 491 := ⟨_, (keep_shifted 491).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c499 : Certified 499 := ⟨_, (keep_shifted 499).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c503 : Certified 503 := ⟨_, (keep_shifted 503).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c509 : Certified 509 := ⟨_, (keep_shifted 509).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c521 : Certified 521 := ⟨_, (keep_shifted 521).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c523 : Certified 523 := ⟨_, (keep_shifted 523).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c541 : Certified 541 := ⟨_, (keep_shifted 541).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c547 : Certified 547 := ⟨_, (keep_shifted 547).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c557 : Certified 557 := ⟨_, (keep_shifted 557).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c563 : Certified 563 := ⟨_, (keep_shifted 563).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c569 : Certified 569 := ⟨_, (keep_shifted 569).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c571 : Certified 571 := ⟨_, (keep_shifted 571).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c577 : Certified 577 := ⟨_, (keep_shifted 577).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c587 : Certified 587 := ⟨_, (keep_shifted 587).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c593 : Certified 593 := ⟨_, (keep_shifted 593).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c599 : Certified 599 := ⟨_, (keep_shifted 599).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c601 : Certified 601 := ⟨_, (keep_shifted 601).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c607 : Certified 607 := ⟨_, (keep_shifted 607).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c613 : Certified 613 := ⟨_, (keep_shifted 613).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c617 : Certified 617 := ⟨_, (keep_shifted 617).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c619 : Certified 619 := ⟨_, (keep_shifted 619).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c631 : Certified 631 := ⟨_, (keep_shifted 631).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c641 : Certified 641 := ⟨_, (keep_shifted 641).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c643 : Certified 643 := ⟨_, (keep_shifted 643).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c647 : Certified 647 := ⟨_, (keep_shifted 647).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c653 : Certified 653 := ⟨_, (keep_shifted 653).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c659 : Certified 659 := ⟨_, (keep_shifted 659).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c661 : Certified 661 := ⟨_, (keep_shifted 661).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c673 : Certified 673 := ⟨_, (keep_shifted 673).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c677 : Certified 677 := ⟨_, (keep_shifted 677).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c683 : Certified 683 := ⟨_, (keep_shifted 683).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c691 : Certified 691 := ⟨_, (keep_shifted 691).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c701 : Certified 701 := ⟨_, (keep_shifted 701).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c709 : Certified 709 := ⟨_, (keep_shifted 709).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c719 : Certified 719 := ⟨_, (keep_shifted 719).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c727 : Certified 727 := ⟨_, (keep_shifted 727).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c733 : Certified 733 := ⟨_, (keep_shifted 733).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c739 : Certified 739 := ⟨_, (keep_shifted 739).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c743 : Certified 743 := ⟨_, (keep_shifted 743).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c751 : Certified 751 := ⟨_, (keep_shifted 751).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c757 : Certified 757 := ⟨_, (keep_shifted 757).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c761 : Certified 761 := ⟨_, (keep_shifted 761).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c769 : Certified 769 := ⟨_, (keep_shifted 769).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c773 : Certified 773 := ⟨_, (keep_shifted 773).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c787 : Certified 787 := ⟨_, (keep_shifted 787).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c797 : Certified 797 := ⟨_, (keep_shifted 797).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c809 : Certified 809 := ⟨_, (keep_shifted 809).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c811 : Certified 811 := ⟨_, (keep_shifted 811).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c821 : Certified 821 := ⟨_, (keep_shifted 821).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c823 : Certified 823 := ⟨_, (keep_shifted 823).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c827 : Certified 827 := ⟨_, (keep_shifted 827).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c829 : Certified 829 := ⟨_, (keep_shifted 829).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c839 : Certified 839 := ⟨_, (keep_shifted 839).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c853 : Certified 853 := ⟨_, (keep_shifted 853).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c857 : Certified 857 := ⟨_, (keep_shifted 857).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c859 : Certified 859 := ⟨_, (keep_shifted 859).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c863 : Certified 863 := ⟨_, (keep_shifted 863).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c877 : Certified 877 := ⟨_, (keep_shifted 877).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c881 : Certified 881 := ⟨_, (keep_shifted 881).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c883 : Certified 883 := ⟨_, (keep_shifted 883).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c887 : Certified 887 := ⟨_, (keep_shifted 887).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c907 : Certified 907 := ⟨_, (keep_shifted 907).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c911 : Certified 911 := ⟨_, (keep_shifted 911).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c919 : Certified 919 := ⟨_, (keep_shifted 919).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c929 : Certified 929 := ⟨_, (keep_shifted 929).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c937 : Certified 937 := ⟨_, (keep_shifted 937).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c941 : Certified 941 := ⟨_, (keep_shifted 941).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c947 : Certified 947 := ⟨_, (keep_shifted 947).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c953 : Certified 953 := ⟨_, (keep_shifted 953).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c967 : Certified 967 := ⟨_, (keep_shifted 967).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c971 : Certified 971 := ⟨_, (keep_shifted 971).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c977 : Certified 977 := ⟨_, (keep_shifted 977).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c983 : Certified 983 := ⟨_, (keep_shifted 983).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c991 : Certified 991 := ⟨_, (keep_shifted 991).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c997 : Certified 997 := ⟨_, (keep_shifted 997).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1009 : Certified 1009 := ⟨_, (keep_shifted 1009).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1013 : Certified 1013 := ⟨_, (keep_shifted 1013).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1019 : Certified 1019 := ⟨_, (keep_shifted 1019).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1021 : Certified 1021 := ⟨_, (keep_shifted 1021).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1031 : Certified 1031 := ⟨_, (keep_shifted 1031).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1033 : Certified 1033 := ⟨_, (keep_shifted 1033).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1039 : Certified 1039 := ⟨_, (keep_shifted 1039).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1049 : Certified 1049 := ⟨_, (keep_shifted 1049).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1051 : Certified 1051 := ⟨_, (keep_shifted 1051).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1061 : Certified 1061 := ⟨_, (keep_shifted 1061).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1063 : Certified 1063 := ⟨_, (keep_shifted 1063).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1069 : Certified 1069 := ⟨_, (keep_shifted 1069).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1087 : Certified 1087 := ⟨_, (keep_shifted 1087).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1091 : Certified 1091 := ⟨_, (keep_shifted 1091).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1093 : Certified 1093 := ⟨_, (keep_shifted 1093).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1097 : Certified 1097 := ⟨_, (keep_shifted 1097).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1103 : Certified 1103 := ⟨_, (keep_shifted 1103).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1109 : Certified 1109 := ⟨_, (keep_shifted 1109).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1117 : Certified 1117 := ⟨_, (keep_shifted 1117).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1123 : Certified 1123 := ⟨_, (keep_shifted 1123).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1129 : Certified 1129 := ⟨_, (keep_shifted 1129).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1151 : Certified 1151 := ⟨_, (keep_shifted 1151).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1153 : Certified 1153 := ⟨_, (keep_shifted 1153).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1163 : Certified 1163 := ⟨_, (keep_shifted 1163).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1171 : Certified 1171 := ⟨_, (keep_shifted 1171).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1181 : Certified 1181 := ⟨_, (keep_shifted 1181).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1187 : Certified 1187 := ⟨_, (keep_shifted 1187).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1193 : Certified 1193 := ⟨_, (keep_shifted 1193).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1201 : Certified 1201 := ⟨_, (keep_shifted 1201).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1213 : Certified 1213 := ⟨_, (keep_shifted 1213).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1217 : Certified 1217 := ⟨_, (keep_shifted 1217).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1223 : Certified 1223 := ⟨_, (keep_shifted 1223).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1229 : Certified 1229 := ⟨_, (keep_shifted 1229).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1231 : Certified 1231 := ⟨_, (keep_shifted 1231).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1237 : Certified 1237 := ⟨_, (keep_shifted 1237).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1249 : Certified 1249 := ⟨_, (keep_shifted 1249).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1259 : Certified 1259 := ⟨_, (keep_shifted 1259).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1277 : Certified 1277 := ⟨_, (keep_shifted 1277).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1279 : Certified 1279 := ⟨_, (keep_shifted 1279).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1283 : Certified 1283 := ⟨_, (keep_shifted 1283).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1289 : Certified 1289 := ⟨_, (keep_shifted 1289).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1291 : Certified 1291 := ⟨_, (keep_shifted 1291).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1297 : Certified 1297 := ⟨_, (keep_shifted 1297).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1301 : Certified 1301 := ⟨_, (keep_shifted 1301).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1303 : Certified 1303 := ⟨_, (keep_shifted 1303).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1307 : Certified 1307 := ⟨_, (keep_shifted 1307).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1319 : Certified 1319 := ⟨_, (keep_shifted 1319).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1321 : Certified 1321 := ⟨_, (keep_shifted 1321).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1327 : Certified 1327 := ⟨_, (keep_shifted 1327).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1361 : Certified 1361 := ⟨_, (keep_shifted 1361).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1367 : Certified 1367 := ⟨_, (keep_shifted 1367).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1373 : Certified 1373 := ⟨_, (keep_shifted 1373).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1381 : Certified 1381 := ⟨_, (keep_shifted 1381).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1399 : Certified 1399 := ⟨_, (keep_shifted 1399).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1409 : Certified 1409 := ⟨_, (keep_shifted 1409).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1423 : Certified 1423 := ⟨_, (keep_shifted 1423).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1427 : Certified 1427 := ⟨_, (keep_shifted 1427).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1429 : Certified 1429 := ⟨_, (keep_shifted 1429).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1433 : Certified 1433 := ⟨_, (keep_shifted 1433).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1439 : Certified 1439 := ⟨_, (keep_shifted 1439).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1447 : Certified 1447 := ⟨_, (keep_shifted 1447).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1451 : Certified 1451 := ⟨_, (keep_shifted 1451).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1453 : Certified 1453 := ⟨_, (keep_shifted 1453).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1459 : Certified 1459 := ⟨_, (keep_shifted 1459).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1471 : Certified 1471 := ⟨_, (keep_shifted 1471).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1481 : Certified 1481 := ⟨_, (keep_shifted 1481).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1483 : Certified 1483 := ⟨_, (keep_shifted 1483).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1487 : Certified 1487 := ⟨_, (keep_shifted 1487).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1489 : Certified 1489 := ⟨_, (keep_shifted 1489).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1493 : Certified 1493 := ⟨_, (keep_shifted 1493).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1499 : Certified 1499 := ⟨_, (keep_shifted 1499).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1511 : Certified 1511 := ⟨_, (keep_shifted 1511).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1523 : Certified 1523 := ⟨_, (keep_shifted 1523).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1531 : Certified 1531 := ⟨_, (keep_shifted 1531).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1543 : Certified 1543 := ⟨_, (keep_shifted 1543).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1549 : Certified 1549 := ⟨_, (keep_shifted 1549).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1553 : Certified 1553 := ⟨_, (keep_shifted 1553).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1559 : Certified 1559 := ⟨_, (keep_shifted 1559).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1567 : Certified 1567 := ⟨_, (keep_shifted 1567).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1571 : Certified 1571 := ⟨_, (keep_shifted 1571).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1579 : Certified 1579 := ⟨_, (keep_shifted 1579).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1583 : Certified 1583 := ⟨_, (keep_shifted 1583).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1597 : Certified 1597 := ⟨_, (keep_shifted 1597).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1601 : Certified 1601 := ⟨_, (keep_shifted 1601).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1607 : Certified 1607 := ⟨_, (keep_shifted 1607).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1609 : Certified 1609 := ⟨_, (keep_shifted 1609).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1613 : Certified 1613 := ⟨_, (keep_shifted 1613).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1619 : Certified 1619 := ⟨_, (keep_shifted 1619).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1621 : Certified 1621 := ⟨_, (keep_shifted 1621).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1627 : Certified 1627 := ⟨_, (keep_shifted 1627).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1637 : Certified 1637 := ⟨_, (keep_shifted 1637).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1657 : Certified 1657 := ⟨_, (keep_shifted 1657).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1663 : Certified 1663 := ⟨_, (keep_shifted 1663).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1667 : Certified 1667 := ⟨_, (keep_shifted 1667).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1669 : Certified 1669 := ⟨_, (keep_shifted 1669).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1693 : Certified 1693 := ⟨_, (keep_shifted 1693).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1697 : Certified 1697 := ⟨_, (keep_shifted 1697).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1699 : Certified 1699 := ⟨_, (keep_shifted 1699).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1709 : Certified 1709 := ⟨_, (keep_shifted 1709).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1721 : Certified 1721 := ⟨_, (keep_shifted 1721).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1723 : Certified 1723 := ⟨_, (keep_shifted 1723).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1733 : Certified 1733 := ⟨_, (keep_shifted 1733).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1741 : Certified 1741 := ⟨_, (keep_shifted 1741).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1747 : Certified 1747 := ⟨_, (keep_shifted 1747).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1753 : Certified 1753 := ⟨_, (keep_shifted 1753).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1759 : Certified 1759 := ⟨_, (keep_shifted 1759).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1777 : Certified 1777 := ⟨_, (keep_shifted 1777).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1783 : Certified 1783 := ⟨_, (keep_shifted 1783).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1787 : Certified 1787 := ⟨_, (keep_shifted 1787).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1789 : Certified 1789 := ⟨_, (keep_shifted 1789).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1801 : Certified 1801 := ⟨_, (keep_shifted 1801).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1811 : Certified 1811 := ⟨_, (keep_shifted 1811).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1823 : Certified 1823 := ⟨_, (keep_shifted 1823).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1831 : Certified 1831 := ⟨_, (keep_shifted 1831).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1847 : Certified 1847 := ⟨_, (keep_shifted 1847).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1861 : Certified 1861 := ⟨_, (keep_shifted 1861).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1867 : Certified 1867 := ⟨_, (keep_shifted 1867).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1871 : Certified 1871 := ⟨_, (keep_shifted 1871).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1873 : Certified 1873 := ⟨_, (keep_shifted 1873).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1877 : Certified 1877 := ⟨_, (keep_shifted 1877).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1879 : Certified 1879 := ⟨_, (keep_shifted 1879).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1889 : Certified 1889 := ⟨_, (keep_shifted 1889).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1901 : Certified 1901 := ⟨_, (keep_shifted 1901).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1907 : Certified 1907 := ⟨_, (keep_shifted 1907).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1913 : Certified 1913 := ⟨_, (keep_shifted 1913).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1931 : Certified 1931 := ⟨_, (keep_shifted 1931).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1933 : Certified 1933 := ⟨_, (keep_shifted 1933).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1949 : Certified 1949 := ⟨_, (keep_shifted 1949).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1951 : Certified 1951 := ⟨_, (keep_shifted 1951).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1973 : Certified 1973 := ⟨_, (keep_shifted 1973).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1979 : Certified 1979 := ⟨_, (keep_shifted 1979).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1987 : Certified 1987 := ⟨_, (keep_shifted 1987).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1993 : Certified 1993 := ⟨_, (keep_shifted 1993).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1997 : Certified 1997 := ⟨_, (keep_shifted 1997).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c1999 : Certified 1999 := ⟨_, (keep_shifted 1999).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2003 : Certified 2003 := ⟨_, (keep_shifted 2003).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2011 : Certified 2011 := ⟨_, (keep_shifted 2011).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2017 : Certified 2017 := ⟨_, (keep_shifted 2017).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2027 : Certified 2027 := ⟨_, (keep_shifted 2027).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2029 : Certified 2029 := ⟨_, (keep_shifted 2029).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2039 : Certified 2039 := ⟨_, (keep_shifted 2039).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2053 : Certified 2053 := ⟨_, (keep_shifted 2053).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2063 : Certified 2063 := ⟨_, (keep_shifted 2063).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2069 : Certified 2069 := ⟨_, (keep_shifted 2069).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2081 : Certified 2081 := ⟨_, (keep_shifted 2081).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2083 : Certified 2083 := ⟨_, (keep_shifted 2083).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2087 : Certified 2087 := ⟨_, (keep_shifted 2087).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2089 : Certified 2089 := ⟨_, (keep_shifted 2089).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2099 : Certified 2099 := ⟨_, (keep_shifted 2099).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2111 : Certified 2111 := ⟨_, (keep_shifted 2111).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2113 : Certified 2113 := ⟨_, (keep_shifted 2113).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2129 : Certified 2129 := ⟨_, (keep_shifted 2129).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2131 : Certified 2131 := ⟨_, (keep_shifted 2131).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2137 : Certified 2137 := ⟨_, (keep_shifted 2137).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2141 : Certified 2141 := ⟨_, (keep_shifted 2141).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2143 : Certified 2143 := ⟨_, (keep_shifted 2143).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2153 : Certified 2153 := ⟨_, (keep_shifted 2153).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2161 : Certified 2161 := ⟨_, (keep_shifted 2161).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2179 : Certified 2179 := ⟨_, (keep_shifted 2179).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2203 : Certified 2203 := ⟨_, (keep_shifted 2203).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2207 : Certified 2207 := ⟨_, (keep_shifted 2207).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2213 : Certified 2213 := ⟨_, (keep_shifted 2213).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2221 : Certified 2221 := ⟨_, (keep_shifted 2221).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2237 : Certified 2237 := ⟨_, (keep_shifted 2237).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2239 : Certified 2239 := ⟨_, (keep_shifted 2239).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2243 : Certified 2243 := ⟨_, (keep_shifted 2243).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2251 : Certified 2251 := ⟨_, (keep_shifted 2251).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2267 : Certified 2267 := ⟨_, (keep_shifted 2267).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2269 : Certified 2269 := ⟨_, (keep_shifted 2269).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2273 : Certified 2273 := ⟨_, (keep_shifted 2273).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2281 : Certified 2281 := ⟨_, (keep_shifted 2281).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2287 : Certified 2287 := ⟨_, (keep_shifted 2287).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2293 : Certified 2293 := ⟨_, (keep_shifted 2293).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2297 : Certified 2297 := ⟨_, (keep_shifted 2297).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2309 : Certified 2309 := ⟨_, (keep_shifted 2309).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2311 : Certified 2311 := ⟨_, (keep_shifted 2311).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2333 : Certified 2333 := ⟨_, (keep_shifted 2333).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2339 : Certified 2339 := ⟨_, (keep_shifted 2339).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2341 : Certified 2341 := ⟨_, (keep_shifted 2341).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2347 : Certified 2347 := ⟨_, (keep_shifted 2347).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2351 : Certified 2351 := ⟨_, (keep_shifted 2351).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2357 : Certified 2357 := ⟨_, (keep_shifted 2357).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2371 : Certified 2371 := ⟨_, (keep_shifted 2371).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2377 : Certified 2377 := ⟨_, (keep_shifted 2377).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2381 : Certified 2381 := ⟨_, (keep_shifted 2381).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2383 : Certified 2383 := ⟨_, (keep_shifted 2383).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2389 : Certified 2389 := ⟨_, (keep_shifted 2389).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2393 : Certified 2393 := ⟨_, (keep_shifted 2393).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2399 : Certified 2399 := ⟨_, (keep_shifted 2399).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2411 : Certified 2411 := ⟨_, (keep_shifted 2411).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2417 : Certified 2417 := ⟨_, (keep_shifted 2417).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2423 : Certified 2423 := ⟨_, (keep_shifted 2423).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2437 : Certified 2437 := ⟨_, (keep_shifted 2437).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2441 : Certified 2441 := ⟨_, (keep_shifted 2441).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2447 : Certified 2447 := ⟨_, (keep_shifted 2447).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2459 : Certified 2459 := ⟨_, (keep_shifted 2459).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2467 : Certified 2467 := ⟨_, (keep_shifted 2467).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2473 : Certified 2473 := ⟨_, (keep_shifted 2473).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2477 : Certified 2477 := ⟨_, (keep_shifted 2477).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2503 : Certified 2503 := ⟨_, (keep_shifted 2503).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2521 : Certified 2521 := ⟨_, (keep_shifted 2521).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2531 : Certified 2531 := ⟨_, (keep_shifted 2531).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2539 : Certified 2539 := ⟨_, (keep_shifted 2539).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2543 : Certified 2543 := ⟨_, (keep_shifted 2543).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2549 : Certified 2549 := ⟨_, (keep_shifted 2549).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2551 : Certified 2551 := ⟨_, (keep_shifted 2551).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2557 : Certified 2557 := ⟨_, (keep_shifted 2557).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2579 : Certified 2579 := ⟨_, (keep_shifted 2579).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2591 : Certified 2591 := ⟨_, (keep_shifted 2591).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2593 : Certified 2593 := ⟨_, (keep_shifted 2593).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2609 : Certified 2609 := ⟨_, (keep_shifted 2609).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2617 : Certified 2617 := ⟨_, (keep_shifted 2617).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2621 : Certified 2621 := ⟨_, (keep_shifted 2621).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2633 : Certified 2633 := ⟨_, (keep_shifted 2633).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2647 : Certified 2647 := ⟨_, (keep_shifted 2647).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2657 : Certified 2657 := ⟨_, (keep_shifted 2657).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2659 : Certified 2659 := ⟨_, (keep_shifted 2659).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2663 : Certified 2663 := ⟨_, (keep_shifted 2663).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2671 : Certified 2671 := ⟨_, (keep_shifted 2671).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2677 : Certified 2677 := ⟨_, (keep_shifted 2677).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2683 : Certified 2683 := ⟨_, (keep_shifted 2683).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2687 : Certified 2687 := ⟨_, (keep_shifted 2687).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2689 : Certified 2689 := ⟨_, (keep_shifted 2689).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2693 : Certified 2693 := ⟨_, (keep_shifted 2693).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2699 : Certified 2699 := ⟨_, (keep_shifted 2699).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2707 : Certified 2707 := ⟨_, (keep_shifted 2707).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2711 : Certified 2711 := ⟨_, (keep_shifted 2711).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2713 : Certified 2713 := ⟨_, (keep_shifted 2713).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2719 : Certified 2719 := ⟨_, (keep_shifted 2719).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2729 : Certified 2729 := ⟨_, (keep_shifted 2729).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2731 : Certified 2731 := ⟨_, (keep_shifted 2731).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2741 : Certified 2741 := ⟨_, (keep_shifted 2741).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2749 : Certified 2749 := ⟨_, (keep_shifted 2749).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2753 : Certified 2753 := ⟨_, (keep_shifted 2753).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2767 : Certified 2767 := ⟨_, (keep_shifted 2767).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2777 : Certified 2777 := ⟨_, (keep_shifted 2777).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2789 : Certified 2789 := ⟨_, (keep_shifted 2789).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2791 : Certified 2791 := ⟨_, (keep_shifted 2791).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2797 : Certified 2797 := ⟨_, (keep_shifted 2797).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2801 : Certified 2801 := ⟨_, (keep_shifted 2801).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2803 : Certified 2803 := ⟨_, (keep_shifted 2803).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2819 : Certified 2819 := ⟨_, (keep_shifted 2819).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2833 : Certified 2833 := ⟨_, (keep_shifted 2833).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2837 : Certified 2837 := ⟨_, (keep_shifted 2837).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2843 : Certified 2843 := ⟨_, (keep_shifted 2843).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2851 : Certified 2851 := ⟨_, (keep_shifted 2851).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2857 : Certified 2857 := ⟨_, (keep_shifted 2857).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2861 : Certified 2861 := ⟨_, (keep_shifted 2861).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2879 : Certified 2879 := ⟨_, (keep_shifted 2879).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2887 : Certified 2887 := ⟨_, (keep_shifted 2887).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2897 : Certified 2897 := ⟨_, (keep_shifted 2897).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2903 : Certified 2903 := ⟨_, (keep_shifted 2903).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2909 : Certified 2909 := ⟨_, (keep_shifted 2909).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2917 : Certified 2917 := ⟨_, (keep_shifted 2917).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2927 : Certified 2927 := ⟨_, (keep_shifted 2927).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2939 : Certified 2939 := ⟨_, (keep_shifted 2939).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2953 : Certified 2953 := ⟨_, (keep_shifted 2953).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2957 : Certified 2957 := ⟨_, (keep_shifted 2957).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2963 : Certified 2963 := ⟨_, (keep_shifted 2963).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2969 : Certified 2969 := ⟨_, (keep_shifted 2969).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2971 : Certified 2971 := ⟨_, (keep_shifted 2971).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c2999 : Certified 2999 := ⟨_, (keep_shifted 2999).trans (by conv => lhs; whnf)⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def c3001 : Certified 3001 := ⟨_, (keep_shifted 3001).trans (by conv => lhs; whnf)⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private def pick (p : ℕ) : Certified p :=
  (if p < 1321 then (if p < 593 then (if p < 251 then (if p < 103 then (if p < 43 then (if p < 17 then (if p < 7 then (if p < 3 then atPrime p 2 c2 else (if p < 5 then atPrime p 3 c3 else atPrime p 5 c5)) else (if p < 11 then atPrime p 7 c7 else (if p < 13 then atPrime p 11 c11 else atPrime p 13 c13))) else (if p < 29 then (if p < 19 then atPrime p 17 c17 else (if p < 23 then atPrime p 19 c19 else atPrime p 23 c23)) else (if p < 37 then (if p < 31 then atPrime p 29 c29 else atPrime p 31 c31) else (if p < 41 then atPrime p 37 c37 else atPrime p 41 c41)))) else (if p < 71 then (if p < 59 then (if p < 47 then atPrime p 43 c43 else (if p < 53 then atPrime p 47 c47 else atPrime p 53 c53)) else (if p < 61 then atPrime p 59 c59 else (if p < 67 then atPrime p 61 c61 else atPrime p 67 c67))) else (if p < 83 then (if p < 73 then atPrime p 71 c71 else (if p < 79 then atPrime p 73 c73 else atPrime p 79 c79)) else (if p < 97 then (if p < 89 then atPrime p 83 c83 else atPrime p 89 c89) else (if p < 101 then atPrime p 97 c97 else atPrime p 101 c101))))) else (if p < 173 then (if p < 137 then (if p < 113 then (if p < 107 then atPrime p 103 c103 else (if p < 109 then atPrime p 107 c107 else atPrime p 109 c109)) else (if p < 127 then atPrime p 113 c113 else (if p < 131 then atPrime p 127 c127 else atPrime p 131 c131))) else (if p < 151 then (if p < 139 then atPrime p 137 c137 else (if p < 149 then atPrime p 139 c139 else atPrime p 149 c149)) else (if p < 163 then (if p < 157 then atPrime p 151 c151 else atPrime p 157 c157) else (if p < 167 then atPrime p 163 c163 else atPrime p 167 c167)))) else (if p < 211 then (if p < 191 then (if p < 179 then atPrime p 173 c173 else (if p < 181 then atPrime p 179 c179 else atPrime p 181 c181)) else (if p < 197 then (if p < 193 then atPrime p 191 c191 else atPrime p 193 c193) else (if p < 199 then atPrime p 197 c197 else atPrime p 199 c199))) else (if p < 229 then (if p < 223 then atPrime p 211 c211 else (if p < 227 then atPrime p 223 c223 else atPrime p 227 c227)) else (if p < 239 then (if p < 233 then atPrime p 229 c229 else atPrime p 233 c233) else (if p < 241 then atPrime p 239 c239 else atPrime p 241 c241)))))) else (if p < 419 then (if p < 331 then (if p < 281 then (if p < 269 then (if p < 257 then atPrime p 251 c251 else (if p < 263 then atPrime p 257 c257 else atPrime p 263 c263)) else (if p < 271 then atPrime p 269 c269 else (if p < 277 then atPrime p 271 c271 else atPrime p 277 c277))) else (if p < 307 then (if p < 283 then atPrime p 281 c281 else (if p < 293 then atPrime p 283 c283 else atPrime p 293 c293)) else (if p < 313 then (if p < 311 then atPrime p 307 c307 else atPrime p 311 c311) else (if p < 317 then atPrime p 313 c313 else atPrime p 317 c317)))) else (if p < 373 then (if p < 349 then (if p < 337 then atPrime p 331 c331 else (if p < 347 then atPrime p 337 c337 else atPrime p 347 c347)) else (if p < 359 then (if p < 353 then atPrime p 349 c349 else atPrime p 353 c353) else (if p < 367 then atPrime p 359 c359 else atPrime p 367 c367))) else (if p < 389 then (if p < 379 then atPrime p 373 c373 else (if p < 383 then atPrime p 379 c379 else atPrime p 383 c383)) else (if p < 401 then (if p < 397 then atPrime p 389 c389 else atPrime p 397 c397) else (if p < 409 then atPrime p 401 c401 else atPrime p 409 c409))))) else (if p < 491 then (if p < 449 then (if p < 433 then (if p < 421 then atPrime p 419 c419 else (if p < 431 then atPrime p 421 c421 else atPrime p 431 c431)) else (if p < 439 then atPrime p 433 c433 else (if p < 443 then atPrime p 439 c439 else atPrime p 443 c443))) else (if p < 463 then (if p < 457 then atPrime p 449 c449 else (if p < 461 then atPrime p 457 c457 else atPrime p 461 c461)) else (if p < 479 then (if p < 467 then atPrime p 463 c463 else atPrime p 467 c467) else (if p < 487 then atPrime p 479 c479 else atPrime p 487 c487)))) else (if p < 547 then (if p < 509 then (if p < 499 then atPrime p 491 c491 else (if p < 503 then atPrime p 499 c499 else atPrime p 503 c503)) else (if p < 523 then (if p < 521 then atPrime p 509 c509 else atPrime p 521 c521) else (if p < 541 then atPrime p 523 c523 else atPrime p 541 c541))) else (if p < 569 then (if p < 557 then atPrime p 547 c547 else (if p < 563 then atPrime p 557 c557 else atPrime p 563 c563)) else (if p < 577 then (if p < 571 then atPrime p 569 c569 else atPrime p 571 c571) else (if p < 587 then atPrime p 577 c577 else atPrime p 587 c587))))))) else (if p < 953 then (if p < 761 then (if p < 661 then (if p < 619 then (if p < 607 then (if p < 599 then atPrime p 593 c593 else (if p < 601 then atPrime p 599 c599 else atPrime p 601 c601)) else (if p < 613 then atPrime p 607 c607 else (if p < 617 then atPrime p 613 c613 else atPrime p 617 c617))) else (if p < 643 then (if p < 631 then atPrime p 619 c619 else (if p < 641 then atPrime p 631 c631 else atPrime p 641 c641)) else (if p < 653 then (if p < 647 then atPrime p 643 c643 else atPrime p 647 c647) else (if p < 659 then atPrime p 653 c653 else atPrime p 659 c659)))) else (if p < 719 then (if p < 683 then (if p < 673 then atPrime p 661 c661 else (if p < 677 then atPrime p 673 c673 else atPrime p 677 c677)) else (if p < 701 then (if p < 691 then atPrime p 683 c683 else atPrime p 691 c691) else (if p < 709 then atPrime p 701 c701 else atPrime p 709 c709))) else (if p < 739 then (if p < 727 then atPrime p 719 c719 else (if p < 733 then atPrime p 727 c727 else atPrime p 733 c733)) else (if p < 751 then (if p < 743 then atPrime p 739 c739 else atPrime p 743 c743) else (if p < 757 then atPrime p 751 c751 else atPrime p 757 c757))))) else (if p < 857 then (if p < 811 then (if p < 787 then (if p < 769 then atPrime p 761 c761 else (if p < 773 then atPrime p 769 c769 else atPrime p 773 c773)) else (if p < 797 then atPrime p 787 c787 else (if p < 809 then atPrime p 797 c797 else atPrime p 809 c809))) else (if p < 827 then (if p < 821 then atPrime p 811 c811 else (if p < 823 then atPrime p 821 c821 else atPrime p 823 c823)) else (if p < 839 then (if p < 829 then atPrime p 827 c827 else atPrime p 829 c829) else (if p < 853 then atPrime p 839 c839 else atPrime p 853 c853)))) else (if p < 907 then (if p < 877 then (if p < 859 then atPrime p 857 c857 else (if p < 863 then atPrime p 859 c859 else atPrime p 863 c863)) else (if p < 883 then (if p < 881 then atPrime p 877 c877 else atPrime p 881 c881) else (if p < 887 then atPrime p 883 c883 else atPrime p 887 c887))) else (if p < 929 then (if p < 911 then atPrime p 907 c907 else (if p < 919 then atPrime p 911 c911 else atPrime p 919 c919)) else (if p < 941 then (if p < 937 then atPrime p 929 c929 else atPrime p 937 c937) else (if p < 947 then atPrime p 941 c941 else atPrime p 947 c947)))))) else (if p < 1129 then (if p < 1039 then (if p < 997 then (if p < 977 then (if p < 967 then atPrime p 953 c953 else (if p < 971 then atPrime p 967 c967 else atPrime p 971 c971)) else (if p < 983 then atPrime p 977 c977 else (if p < 991 then atPrime p 983 c983 else atPrime p 991 c991))) else (if p < 1019 then (if p < 1009 then atPrime p 997 c997 else (if p < 1013 then atPrime p 1009 c1009 else atPrime p 1013 c1013)) else (if p < 1031 then (if p < 1021 then atPrime p 1019 c1019 else atPrime p 1021 c1021) else (if p < 1033 then atPrime p 1031 c1031 else atPrime p 1033 c1033)))) else (if p < 1091 then (if p < 1061 then (if p < 1049 then atPrime p 1039 c1039 else (if p < 1051 then atPrime p 1049 c1049 else atPrime p 1051 c1051)) else (if p < 1069 then (if p < 1063 then atPrime p 1061 c1061 else atPrime p 1063 c1063) else (if p < 1087 then atPrime p 1069 c1069 else atPrime p 1087 c1087))) else (if p < 1103 then (if p < 1093 then atPrime p 1091 c1091 else (if p < 1097 then atPrime p 1093 c1093 else atPrime p 1097 c1097)) else (if p < 1117 then (if p < 1109 then atPrime p 1103 c1103 else atPrime p 1109 c1109) else (if p < 1123 then atPrime p 1117 c1117 else atPrime p 1123 c1123))))) else (if p < 1231 then (if p < 1187 then (if p < 1163 then (if p < 1151 then atPrime p 1129 c1129 else (if p < 1153 then atPrime p 1151 c1151 else atPrime p 1153 c1153)) else (if p < 1171 then atPrime p 1163 c1163 else (if p < 1181 then atPrime p 1171 c1171 else atPrime p 1181 c1181))) else (if p < 1213 then (if p < 1193 then atPrime p 1187 c1187 else (if p < 1201 then atPrime p 1193 c1193 else atPrime p 1201 c1201)) else (if p < 1223 then (if p < 1217 then atPrime p 1213 c1213 else atPrime p 1217 c1217) else (if p < 1229 then atPrime p 1223 c1223 else atPrime p 1229 c1229)))) else (if p < 1289 then (if p < 1259 then (if p < 1237 then atPrime p 1231 c1231 else (if p < 1249 then atPrime p 1237 c1237 else atPrime p 1249 c1249)) else (if p < 1279 then (if p < 1277 then atPrime p 1259 c1259 else atPrime p 1277 c1277) else (if p < 1283 then atPrime p 1279 c1279 else atPrime p 1283 c1283))) else (if p < 1301 then (if p < 1291 then atPrime p 1289 c1289 else (if p < 1297 then atPrime p 1291 c1291 else atPrime p 1297 c1297)) else (if p < 1307 then (if p < 1303 then atPrime p 1301 c1301 else atPrime p 1303 c1303) else (if p < 1319 then atPrime p 1307 c1307 else atPrime p 1319 c1319)))))))) else (if p < 2143 then (if p < 1733 then (if p < 1543 then (if p < 1447 then (if p < 1399 then (if p < 1367 then (if p < 1327 then atPrime p 1321 c1321 else (if p < 1361 then atPrime p 1327 c1327 else atPrime p 1361 c1361)) else (if p < 1373 then atPrime p 1367 c1367 else (if p < 1381 then atPrime p 1373 c1373 else atPrime p 1381 c1381))) else (if p < 1427 then (if p < 1409 then atPrime p 1399 c1399 else (if p < 1423 then atPrime p 1409 c1409 else atPrime p 1423 c1423)) else (if p < 1433 then (if p < 1429 then atPrime p 1427 c1427 else atPrime p 1429 c1429) else (if p < 1439 then atPrime p 1433 c1433 else atPrime p 1439 c1439)))) else (if p < 1487 then (if p < 1459 then (if p < 1451 then atPrime p 1447 c1447 else (if p < 1453 then atPrime p 1451 c1451 else atPrime p 1453 c1453)) else (if p < 1481 then (if p < 1471 then atPrime p 1459 c1459 else atPrime p 1471 c1471) else (if p < 1483 then atPrime p 1481 c1481 else atPrime p 1483 c1483))) else (if p < 1499 then (if p < 1489 then atPrime p 1487 c1487 else (if p < 1493 then atPrime p 1489 c1489 else atPrime p 1493 c1493)) else (if p < 1523 then (if p < 1511 then atPrime p 1499 c1499 else atPrime p 1511 c1511) else (if p < 1531 then atPrime p 1523 c1523 else atPrime p 1531 c1531))))) else (if p < 1619 then (if p < 1579 then (if p < 1559 then (if p < 1549 then atPrime p 1543 c1543 else (if p < 1553 then atPrime p 1549 c1549 else atPrime p 1553 c1553)) else (if p < 1567 then atPrime p 1559 c1559 else (if p < 1571 then atPrime p 1567 c1567 else atPrime p 1571 c1571))) else (if p < 1601 then (if p < 1583 then atPrime p 1579 c1579 else (if p < 1597 then atPrime p 1583 c1583 else atPrime p 1597 c1597)) else (if p < 1609 then (if p < 1607 then atPrime p 1601 c1601 else atPrime p 1607 c1607) else (if p < 1613 then atPrime p 1609 c1609 else atPrime p 1613 c1613)))) else (if p < 1669 then (if p < 1637 then (if p < 1621 then atPrime p 1619 c1619 else (if p < 1627 then atPrime p 1621 c1621 else atPrime p 1627 c1627)) else (if p < 1663 then (if p < 1657 then atPrime p 1637 c1637 else atPrime p 1657 c1657) else (if p < 1667 then atPrime p 1663 c1663 else atPrime p 1667 c1667))) else (if p < 1699 then (if p < 1693 then atPrime p 1669 c1669 else (if p < 1697 then atPrime p 1693 c1693 else atPrime p 1697 c1697)) else (if p < 1721 then (if p < 1709 then atPrime p 1699 c1699 else atPrime p 1709 c1709) else (if p < 1723 then atPrime p 1721 c1721 else atPrime p 1723 c1723)))))) else (if p < 1951 then (if p < 1847 then (if p < 1783 then (if p < 1753 then (if p < 1741 then atPrime p 1733 c1733 else (if p < 1747 then atPrime p 1741 c1741 else atPrime p 1747 c1747)) else (if p < 1759 then atPrime p 1753 c1753 else (if p < 1777 then atPrime p 1759 c1759 else atPrime p 1777 c1777))) else (if p < 1801 then (if p < 1787 then atPrime p 1783 c1783 else (if p < 1789 then atPrime p 1787 c1787 else atPrime p 1789 c1789)) else (if p < 1823 then (if p < 1811 then atPrime p 1801 c1801 else atPrime p 1811 c1811) else (if p < 1831 then atPrime p 1823 c1823 else atPrime p 1831 c1831)))) else (if p < 1889 then (if p < 1871 then (if p < 1861 then atPrime p 1847 c1847 else (if p < 1867 then atPrime p 1861 c1861 else atPrime p 1867 c1867)) else (if p < 1877 then (if p < 1873 then atPrime p 1871 c1871 else atPrime p 1873 c1873) else (if p < 1879 then atPrime p 1877 c1877 else atPrime p 1879 c1879))) else (if p < 1913 then (if p < 1901 then atPrime p 1889 c1889 else (if p < 1907 then atPrime p 1901 c1901 else atPrime p 1907 c1907)) else (if p < 1933 then (if p < 1931 then atPrime p 1913 c1913 else atPrime p 1931 c1931) else (if p < 1949 then atPrime p 1933 c1933 else atPrime p 1949 c1949))))) else (if p < 2053 then (if p < 1999 then (if p < 1987 then (if p < 1973 then atPrime p 1951 c1951 else (if p < 1979 then atPrime p 1973 c1973 else atPrime p 1979 c1979)) else (if p < 1993 then atPrime p 1987 c1987 else (if p < 1997 then atPrime p 1993 c1993 else atPrime p 1997 c1997))) else (if p < 2017 then (if p < 2003 then atPrime p 1999 c1999 else (if p < 2011 then atPrime p 2003 c2003 else atPrime p 2011 c2011)) else (if p < 2029 then (if p < 2027 then atPrime p 2017 c2017 else atPrime p 2027 c2027) else (if p < 2039 then atPrime p 2029 c2029 else atPrime p 2039 c2039)))) else (if p < 2099 then (if p < 2081 then (if p < 2063 then atPrime p 2053 c2053 else (if p < 2069 then atPrime p 2063 c2063 else atPrime p 2069 c2069)) else (if p < 2087 then (if p < 2083 then atPrime p 2081 c2081 else atPrime p 2083 c2083) else (if p < 2089 then atPrime p 2087 c2087 else atPrime p 2089 c2089))) else (if p < 2129 then (if p < 2111 then atPrime p 2099 c2099 else (if p < 2113 then atPrime p 2111 c2111 else atPrime p 2113 c2113)) else (if p < 2137 then (if p < 2131 then atPrime p 2129 c2129 else atPrime p 2131 c2131) else (if p < 2141 then atPrime p 2137 c2137 else atPrime p 2141 c2141))))))) else (if p < 2593 then (if p < 2371 then (if p < 2269 then (if p < 2213 then (if p < 2179 then (if p < 2153 then atPrime p 2143 c2143 else (if p < 2161 then atPrime p 2153 c2153 else atPrime p 2161 c2161)) else (if p < 2203 then atPrime p 2179 c2179 else (if p < 2207 then atPrime p 2203 c2203 else atPrime p 2207 c2207))) else (if p < 2239 then (if p < 2221 then atPrime p 2213 c2213 else (if p < 2237 then atPrime p 2221 c2221 else atPrime p 2237 c2237)) else (if p < 2251 then (if p < 2243 then atPrime p 2239 c2239 else atPrime p 2243 c2243) else (if p < 2267 then atPrime p 2251 c2251 else atPrime p 2267 c2267)))) else (if p < 2311 then (if p < 2287 then (if p < 2273 then atPrime p 2269 c2269 else (if p < 2281 then atPrime p 2273 c2273 else atPrime p 2281 c2281)) else (if p < 2297 then (if p < 2293 then atPrime p 2287 c2287 else atPrime p 2293 c2293) else (if p < 2309 then atPrime p 2297 c2297 else atPrime p 2309 c2309))) else (if p < 2341 then (if p < 2333 then atPrime p 2311 c2311 else (if p < 2339 then atPrime p 2333 c2333 else atPrime p 2339 c2339)) else (if p < 2351 then (if p < 2347 then atPrime p 2341 c2341 else atPrime p 2347 c2347) else (if p < 2357 then atPrime p 2351 c2351 else atPrime p 2357 c2357))))) else (if p < 2459 then (if p < 2399 then (if p < 2383 then (if p < 2377 then atPrime p 2371 c2371 else (if p < 2381 then atPrime p 2377 c2377 else atPrime p 2381 c2381)) else (if p < 2389 then atPrime p 2383 c2383 else (if p < 2393 then atPrime p 2389 c2389 else atPrime p 2393 c2393))) else (if p < 2423 then (if p < 2411 then atPrime p 2399 c2399 else (if p < 2417 then atPrime p 2411 c2411 else atPrime p 2417 c2417)) else (if p < 2441 then (if p < 2437 then atPrime p 2423 c2423 else atPrime p 2437 c2437) else (if p < 2447 then atPrime p 2441 c2441 else atPrime p 2447 c2447)))) else (if p < 2539 then (if p < 2477 then (if p < 2467 then atPrime p 2459 c2459 else (if p < 2473 then atPrime p 2467 c2467 else atPrime p 2473 c2473)) else (if p < 2521 then (if p < 2503 then atPrime p 2477 c2477 else atPrime p 2503 c2503) else (if p < 2531 then atPrime p 2521 c2521 else atPrime p 2531 c2531))) else (if p < 2551 then (if p < 2543 then atPrime p 2539 c2539 else (if p < 2549 then atPrime p 2543 c2543 else atPrime p 2549 c2549)) else (if p < 2579 then (if p < 2557 then atPrime p 2551 c2551 else atPrime p 2557 c2557) else (if p < 2591 then atPrime p 2579 c2579 else atPrime p 2591 c2591)))))) else (if p < 2789 then (if p < 2689 then (if p < 2657 then (if p < 2621 then (if p < 2609 then atPrime p 2593 c2593 else (if p < 2617 then atPrime p 2609 c2609 else atPrime p 2617 c2617)) else (if p < 2633 then atPrime p 2621 c2621 else (if p < 2647 then atPrime p 2633 c2633 else atPrime p 2647 c2647))) else (if p < 2671 then (if p < 2659 then atPrime p 2657 c2657 else (if p < 2663 then atPrime p 2659 c2659 else atPrime p 2663 c2663)) else (if p < 2683 then (if p < 2677 then atPrime p 2671 c2671 else atPrime p 2677 c2677) else (if p < 2687 then atPrime p 2683 c2683 else atPrime p 2687 c2687)))) else (if p < 2729 then (if p < 2707 then (if p < 2693 then atPrime p 2689 c2689 else (if p < 2699 then atPrime p 2693 c2693 else atPrime p 2699 c2699)) else (if p < 2713 then (if p < 2711 then atPrime p 2707 c2707 else atPrime p 2711 c2711) else (if p < 2719 then atPrime p 2713 c2713 else atPrime p 2719 c2719))) else (if p < 2749 then (if p < 2731 then atPrime p 2729 c2729 else (if p < 2741 then atPrime p 2731 c2731 else atPrime p 2741 c2741)) else (if p < 2767 then (if p < 2753 then atPrime p 2749 c2749 else atPrime p 2753 c2753) else (if p < 2777 then atPrime p 2767 c2767 else atPrime p 2777 c2777))))) else (if p < 2887 then (if p < 2833 then (if p < 2801 then (if p < 2791 then atPrime p 2789 c2789 else (if p < 2797 then atPrime p 2791 c2791 else atPrime p 2797 c2797)) else (if p < 2803 then atPrime p 2801 c2801 else (if p < 2819 then atPrime p 2803 c2803 else atPrime p 2819 c2819))) else (if p < 2851 then (if p < 2837 then atPrime p 2833 c2833 else (if p < 2843 then atPrime p 2837 c2837 else atPrime p 2843 c2843)) else (if p < 2861 then (if p < 2857 then atPrime p 2851 c2851 else atPrime p 2857 c2857) else (if p < 2879 then atPrime p 2861 c2861 else atPrime p 2879 c2879)))) else (if p < 2953 then (if p < 2909 then (if p < 2897 then atPrime p 2887 c2887 else (if p < 2903 then atPrime p 2897 c2897 else atPrime p 2903 c2903)) else (if p < 2927 then (if p < 2917 then atPrime p 2909 c2909 else atPrime p 2917 c2917) else (if p < 2939 then atPrime p 2927 c2927 else atPrime p 2939 c2939))) else (if p < 2969 then (if p < 2957 then atPrime p 2953 c2953 else (if p < 2963 then atPrime p 2957 c2957 else atPrime p 2963 c2963)) else (if p < 2999 then (if p < 2971 then atPrime p 2969 c2969 else atPrime p 2971 c2971) else (if p < 3001 then atPrime p 2999 c2999 else atPrime p 3001 c3001)))))))))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
def word (p : ℕ) := (pick p).val
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem word_correct (p : ℕ) : word p = keep p := (pick p).property.symm

end Astra247824.HardTail.Patterns

namespace Astra247824.HardTail
open Finset Leaves ArithmeticFunction
def stageSet := (Nat.primesLE 3006).filter (fun p => 23 < p)

def key (e : Edge) := (X/(e.1*e.2)/W,e.2)

def queryLow (p b : ℕ) := max (max p (Y/p)) (X/(p*((b+1)*W)))

def queryHigh (p b : ℕ) := if b=0 then min Y (X/p^3)
  else min (min Y (X/p^3)) (X/(p*(b*W)))

def queryDenoms (p b : ℕ) := (Ioc (queryLow p b) (queryHigh p b)).filter
  (fun d => Squarefree d ∧ p < d.minFac)

theorem mem_queryDenoms {d p b : ℕ} (pp : p.Prime) :
    d ∈ queryDenoms p b ↔ (⟨d,p⟩ : Edge) ∈ hardEdges X Y ∧ X/(d*p)/W=b := by
  rw [indexed_hard_block pp (by decide : 0 < W)]
  simp only [queryDenoms,mem_filter,mem_Ioc,queryLow,queryHigh]
  tauto

theorem endpoints_bound {e : Edge} (he : e ∈ S) : X/(e.1*e.2)/W < 28741 := by
  have cross := (mem_filter.mp (mem_filter.mp (mem_filter.mp he).1).1).2
  change ¬ e.1*e.2 ≤ 43399 at cross
  have low : 43400 ≤ e.1*e.2 := by omega
  exact lt_of_le_of_lt (Nat.div_le_div_right (Nat.div_le_div_left low (by decide : 0 < 43400)))
    (by decide : X/43400/W < 28741)

private theorem key_col {e : Edge} (he : e ∈ S) : e.2 ∈ stageSet := by
  have h := (mem_filter.mp he).1
  have primes :=
    Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp (mem_filter.mp h).1).1).2
  have ps : e.2 ∈ Nat.primesLE 3006 :=
    (Nat.mem_primesLE (n:=3006) (p:=e.2)).mpr ⟨hard_prime_upper (y:=Y) (e:=e) h,primes⟩
  exact (mem_filter (s:=Nat.primesLE 3006) (p:=fun z : ℕ => 23 < z) (a:=e.2)).mpr
    ⟨ps,(mem_filter.mp he).2⟩

private theorem regroup {A : Type*} [DecidableEq A] (R : Finset A) (B P : Finset ℕ)
    (k : A → ℕ × ℕ) (f : A → ℤ) (row : ∀ e ∈ R, (k e).1 ∈ B)
    (col : ∀ e ∈ R, (k e).2 ∈ P) :
    (∑ e ∈ R, f e) = ∑ b ∈ B, ∑ p ∈ P, ∑ e ∈ R.filter (fun e => k e = (b,p)), f e := by
  have mapped : ∀ e ∈ R, k e ∈ B ×ˢ P := fun e he =>
    Finset.mem_product.mpr ⟨row e he,col e he⟩
  have all := sum_fiberwise_of_maps_to (s:=R) (t:=B ×ˢ P) (g:=k) mapped f
  rw [←all, Finset.sum_product]

theorem fibers {p b : ℕ} (pp : p.Prime) (large : 23 < p) :
    S.filter (fun e => key e=(b,p)) = (queryDenoms p b).image (fun d => (⟨d,p⟩ : Edge)) := by
  ext e
  obtain ⟨d,q⟩ := e
  constructor
  · rintro h
    obtain ⟨inside,params⟩ := mem_filter.mp h
    have qp : q=p := congrArg Prod.snd params
    subst q
    exact mem_image.mpr ⟨d,(mem_queryDenoms pp).mpr ⟨(mem_filter.mp inside).1,
      congrArg Prod.fst params⟩,rfl⟩
  · rintro h
    obtain ⟨n,member,eq⟩ := mem_image.mp h
    obtain rfl : n=d := congrArg Sigma.fst eq
    obtain rfl : p=q := congrArg (fun e : Edge => e.2) eq
    obtain ⟨he,loc⟩ := (mem_queryDenoms pp).mp member
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,large⟩,Prod.ext loc rfl⟩

def cellValue (p b word : ℕ) : ℤ :=
  let packed := packedClasses 32 2048 word
  ∑ d ∈ queryDenoms p b, -moebius d *
    (packedRank word packed (X/(d*p)%W+1) : ℤ)

theorem cell_sound {p b word : ℕ} (pp : p.Prime) (large : 23 < p)
    (bits : ∀ i < W, word.testBit i = true ↔ ∀ q ∈ descendingPrimes (p-1), ¬q ∣ b*W+i) :
    ∑ e ∈ S.filter (fun e => key e=(b,p)), term e = cellValue p b word := by
  rw [fibers pp large,sum_image (fun d _ n _ e => congrArg Sigma.fst e)]
  apply sum_congr rfl
  intro d hd
  have loc := ((mem_queryDenoms pp).mp hd).2
  let t := X/(d*p)
  have bound := Nat.mod_lt t (by decide : 0 < W)
  have size : t%W+1 ≤ 65536 := by dsimp [W] at *; omega
  have eq := packedRank_segment (lo:=b*W) size bits
  change -moebius d * (tail p t : ℤ) = -moebius d * (packedRank word _ (t%W+1) : ℤ)
  rw [tail_eq_segment p t large]
  change t/W=b at loc
  rw [loc,eq]

def byBlocks (mask : ℕ → ℕ → ℕ) : ℤ :=
  ∑ b ∈ range 28741, ∑ p ∈ stageSet, cellValue p b (mask b p)

theorem sum_by_blocks (mask : ℕ → ℕ → ℕ)
    (bits : ∀ b < 28741, ∀ p∈stageSet, ∀ i < W, (mask b p).testBit i = true ↔
      ∀ q∈descendingPrimes (p-1), ¬q ∣ b*W+i) :
    (∑ e ∈ S, term e) = byBlocks mask := by
  change (∑ e ∈ S, term e) = ∑ b ∈ range 28741, ∑ p ∈ stageSet, cellValue p b (mask b p)
  refine (regroup S (range 28741) stageSet key term
    (fun e he => (mem_range (m:=(key e).1) (n:=28741)).mpr (@endpoints_bound e he))
    (fun e he => @key_col e he)).trans ?_
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro p hp
  obtain ⟨mem,large⟩ := mem_filter.mp hp
  exact cell_sound (Nat.prime_of_mem_primesLE mem) large (bits b (mem_range.mp hb) p hp)

def stageCap (b : ℕ) : ℕ := min 3006 (min (((b+1)*W-1).sqrt)
  (if b=0 then 3006 else (X/(b*W)).sqrt))

theorem capped_of_member {p b d : ℕ} (pp : p.Prime) (hd : d ∈ queryDenoms p b) :
    p ≤ stageCap b := by
  obtain ⟨edge,loc⟩ := (mem_queryDenoms pp).mp hd
  have small := hard_prime_upper edge
  have info := (hard_denominator_iff pp).mp edge
  have pd : p < d := (max_lt_iff.mp info.2.2.1).1
  have pos : 0 < d*p := Nat.mul_pos (by omega) pp.pos
  let t := X/(d*p)
  have hard : p^2 ≤ t := not_lt.mp (mem_filter.mp edge).2
  have last : t < (b+1)*W := (Nat.div_lt_iff_lt_mul (by decide : 0 < W)).mp
    (by change t/W=b at loc; omega)
  have squareBound : p ≤ ((b+1)*W-1).sqrt := Nat.le_sqrt'.mpr (by omega)
  apply le_min small (le_min squareBound ?_)
  by_cases zero : b=0
  · simpa only [zero,if_true] using small
  · rw [if_neg zero]
    apply Nat.le_sqrt.mpr
    have base : b*W ≤ t := by rw [←loc]; exact Nat.div_mul_le_self t W
    have low := (Nat.le_div_iff_mul_le pos).mp base
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by decide : 0 < W))).mpr
    rw [Nat.mul_comm (p*p)]
    exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right p (Nat.le_of_lt pd))).trans low

def stageFloor (b : ℕ) := X/(Y*((b+1)*W))

theorem floor_of_member {p b d : ℕ} (pp : p.Prime) (hd : d ∈ queryDenoms p b) :
    stageFloor b < p := by
  obtain ⟨edge,loc⟩ := (mem_queryDenoms pp).mp hd
  have info := (hard_denominator_iff pp).mp edge
  have pd : p < d := (max_lt_iff.mp info.2.2.1).1
  have dy := (le_min_iff.mp info.2.2.2).1
  have last : X/(d*p) < (b+1)*W := (Nat.div_lt_iff_lt_mul (by decide : 0 < W)).mp (by omega)
  have close := (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega : 0 < d) pp.pos)).mp last
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide : 0 < Y)
    (Nat.mul_pos (by omega : 0 < b+1) (by decide : 0 < W)))).mpr
  calc
    X < ((b+1)*W)*(d*p) := close
    _ ≤ ((b+1)*W)*(Y*p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right p dy)
    _ = p*(Y*((b+1)*W)) := by ring

def stripedMask (b p : ℕ) := blockMask (b*W) W (descendingPrimes (p-1))
end Astra247824.HardTail


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

/- A single mask sweep per endpoint block. Denominator lookup and cached divisibility
patterns may be replaced independently by implementations with the stated specifications.
`clearFixed_spec` and `clearDivisors_spec` come from the verified segmented sieve in
FastPhi.lean in this repository. -/
namespace Astra247824.HardTail.Scan
open Finset Leaves

/- `past` primes have already been removed from the current segment mask. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def Flags (b word : ℕ) (past : List ℕ) :=
  ∀ i < W, word.testBit i = true ↔ ∀ q∈past, ¬q ∣ b*W+i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def remove (word pattern offset : ℕ) := word &&& (pattern >>> offset)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem advance {b word p pattern : ℕ} {past : List ℕ} (bits : Flags b word past)
    (pp : p.Prime) (data : pattern=Patterns.keep p) :
    Flags b (remove word pattern ((b*W)%p)) (past++[p]) := by
  intro i hi
  let phase := b*W%p
  have bound : phase+i < W+p := by have := Nat.mod_lt (b*W) pp.pos; dsimp [phase]; omega
  have allOn : (2^(W+p)-1).testBit (phase+i)=true := by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true bound
  have same : (remove word (Patterns.keep p) phase).testBit i =
      (clearFixed word (fixedPattern p W) phase).testBit i := by
    simp only [remove,Patterns.keep,clearFixed,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_shiftRight,allOn]
    cases word.testBit i <;> cases (fixedPattern p W).testBit (phase+i) <;> decide
  rw [data,same,clearFixed_spec pp.pos hi,clearDivisors_spec pp.pos hi,bits i hi]
  simp only [List.mem_append,List.mem_singleton]
  constructor
  · rintro ⟨done,last⟩ q (hq|rfl)
    · exact done q hq
    · exact last
  · intro h
    exact ⟨fun q hq => h q (Or.inl hq),h p (Or.inr rfl)⟩

/- The current stage first answers queries at p, then removes multiples of p. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def sweep (eval : ℕ → ℕ → ℕ → ℤ) (pattern : ℕ → ℕ) (b cap low : ℕ) : List ℕ → ℕ → ℤ
  | [], _ => 0
  | p::ps, word =>
    if cap < p then 0 else
      (if 23 < p ∧ low < p then eval b p word else 0) +
      sweep eval pattern b cap low ps (remove word (pattern p) ((b*W)%p))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def trueCell (b p : ℕ) := ∑ e ∈ S.filter (fun e => key e=(b,p)), term e
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def value (b p : ℕ) : ℤ :=
  if 23 < p ∧ stageFloor b < p ∧ p ≤ stageCap b then trueCell b p else 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem before_mem {past next : List ℕ} {p q : ℕ} (split : past++p::next=roster) :
    q∈past ↔ q∈descendingPrimes (p-1) := by
  have order : (past++p::next).Pairwise (·<·) := by rw [split]; exact roster_sorted
  obtain ⟨_,right,cross⟩ := List.pairwise_append.mp order
  have pprime := (roster_mem p).mp (split ▸ List.mem_append_right past List.mem_cons_self)
  rw [mem_descending,Nat.mem_primesLE]
  constructor
  · intro hq
    have prime := ((roster_mem q).mp (split ▸ List.mem_append_left _ hq)).2
    have lt := cross q hq p List.mem_cons_self
    exact ⟨by omega,prime⟩
  · rintro ⟨lim,prime⟩
    have lt : q < p := by have := pprime.2.pos; omega
    have member := (roster_mem q).mpr ⟨by omega,prime⟩
    rw [←split,List.mem_append,List.mem_cons] at member
    rcases member with done|same|late
    · exact done
    · omega
    · exact (lt.not_ge ((List.pairwise_cons.mp right).1 q late).le).elim

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem sweep_spec (eval : ℕ → ℕ → ℕ → ℤ) (pattern : ℕ → ℕ)
    (evaluation : ∀ b p word, p.Prime → 23 < p → stageFloor b < p → p ≤ stageCap b →
      (∀ i < W, word.testBit i=true ↔ ∀ q∈descendingPrimes (p-1), ¬q ∣ b*W+i) →
      eval b p word=trueCell b p)
    (patterns : ∀ p∈roster, pattern p=Patterns.keep p)
    (b : ℕ) (todo past : List ℕ) (word : ℕ) (all : past++todo=roster) (bits : Flags b word past) :
    sweep eval pattern b (stageCap b) (stageFloor b) todo word = (todo.map (value b)).sum := by
  induction todo generalizing past word with
  | nil => rfl
  | cons p ps ih =>
    have member : p∈roster := all ▸ List.mem_append_right past List.mem_cons_self
    have prime := ((roster_mem p).mp member).2
    have later : ∀ q∈ps,p < q := by
      have hh : (past++p::ps).Pairwise (·<·) := by rw [all]; exact roster_sorted
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hh).2.1).1
    simp only [sweep,List.map_cons,List.sum_cons]
    by_cases out : stageCap b < p
    · rw [if_pos out]
      have zero : ∀ q∈p::ps,value b q=0 := by
        intro q hq
        have h : stageCap b < q := by
          rcases List.mem_cons.mp hq with rfl|mem
          · exact out
          · exact out.trans (later q mem)
        exact if_neg (fun w => h.not_ge w.2.2)
      have rem : (ps.map (value b)).sum=0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
        exact zero q (List.mem_cons_of_mem _ hq)
      rw [zero p List.mem_cons_self,rem,add_zero]
    · rw [if_neg out]
      have step := ih (past++[p]) (remove word (pattern p) (b*W%p))
        (by simpa only [List.append_assoc,List.singleton_append] using all)
        (advance bits prime (patterns p member))
      rw [step]
      congr 1
      by_cases ok : 23 < p ∧ stageFloor b < p
      · rw [if_pos ok,value,if_pos ⟨ok.1,ok.2,by omega⟩]
        apply evaluation b p word prime ok.1 ok.2 (by omega)
        intro i hi
        rw [bits _ hi]
        simp only [before_mem all]
      · rw [if_neg ok,value,if_neg (fun h => ok ⟨h.1,h.2.1⟩)]


end Astra247824.HardTail.Scan

/- Relate the sum of all verified sieve sweeps to the within-block target. -/
namespace Astra247824.HardTail.Scan
open Finset Leaves

set_option maxRecDepth 2048 in
set_option maxHeartbeats 240000 in
private theorem outside (b p : ℕ) (prime : p.Prime) (large : 23 < p)
    (bad : ¬ (stageFloor b < p ∧ p ≤ stageCap b)) : trueCell b p = 0 := by
  have empty : queryDenoms p b=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact bad ⟨floor_of_member prime hd,capped_of_member prime hd⟩
  simp only [trueCell,fibers prime large,empty,image_empty,sum_empty]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 240000 in
private theorem block_exact (b : ℕ) : (roster.map (value b)).sum =
    ∑ p ∈ stageSet, trueCell b p := by
  have idx : roster.toFinset = Nat.primesLE 3006 := by
    ext p; simp only [List.mem_toFinset,roster_mem,Nat.mem_primesLE]
  have nodup : roster.Nodup := roster_sorted.imp (fun h => ne_of_lt h)
  rw [←List.sum_toFinset _ nodup,idx]
  unfold stageSet
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases large : 23 < p
  · rw [if_pos large]
    by_cases inBand : stageFloor b < p ∧ p ≤ stageCap b
    · exact if_pos ⟨large,inBand⟩
    · rw [outside b p (Nat.prime_of_mem_primesLE hp) large inBand]
      exact if_neg (fun h => inBand h.2)
  · rw [if_neg large]
    exact if_neg (fun h => large h.1)

/- Operational target, independent of the representation of the denominator queries. -/
set_option maxRecDepth 2048 in
set_option maxHeartbeats 240000 in
def total (eval : ℕ → ℕ → ℕ → ℤ) (pattern : ℕ → ℕ) : ℤ :=
  ∑ b ∈ range 28741, sweep eval pattern b (stageCap b) (stageFloor b) roster (2^W-1)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 240000 in
theorem h2_iff_sweep (eval : ℕ → ℕ → ℕ → ℤ) (pattern : ℕ → ℕ)
    (evaluation : ∀ b p word, p.Prime → 23 < p → stageFloor b < p → p ≤ stageCap b →
      (∀ i < W, word.testBit i=true ↔ ∀ q∈descendingPrimes (p-1), ¬q ∣ b*W+i) →
      eval b p word=cellValue p b word)
    (patterns : ∀ p∈roster, pattern p=Patterns.keep p) :
    OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H2 ↔ total eval pattern=3098980124 := by
  have packed := sum_by_blocks stripedMask (fun _ _ _ _ _ hi => blockMask_spec hi
    (fun _ hq => (Nat.prime_of_mem_primesLE (mem_descending.mp hq)).pos))
  have ans : total eval pattern = ∑ e ∈ S, term e := by
    unfold total
    rw [packed]
    apply sum_congr rfl
    intro b hb
    rw [sweep_spec eval pattern _ patterns b roster [] _ rfl (by
      intro i hi; simp [Nat.testBit_two_pow_sub_one,hi]),block_exact]
    · apply sum_congr rfl
      intro p hp
      obtain ⟨inP,large⟩ := mem_filter.mp hp
      exact cell_sound (Nat.prime_of_mem_primesLE inP) large (fun i hi => blockMask_spec hi
        (fun _ hq => (Nat.prime_of_mem_primesLE (mem_descending.mp hq)).pos))
    · intro b p word prime large low cap flags
      exact (evaluation b p word prime large low cap flags).trans (cell_sound prime large flags).symm
  rw [original_iff_sum,ans]

end Astra247824.HardTail.Scan

/- Parallel population counts for every 32-bit field in a 65,536-bit sieve word. -/
namespace Astra247824
namespace WordPop
open Finset

/- Concatenate radix-2^w digits in increasing index order. -/
private def fields (w : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | k+1, f => 2^w * fields w k (fun i => f (i+1)) + f 0

private theorem fields_sum (w k : ℕ) (f : ℕ → ℕ) :
    fields w k f = ∑ i ∈ range k, f i * (2^w)^i := by
  induction k generalizing f with
  | zero => simp [fields]
  | succ k ih =>
    rw [fields,ih,Finset.sum_range_succ',Finset.mul_sum]
    simp only [pow_zero,Nat.mul_one]
    apply congrArg₂ Nat.add _ rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]; ring

private theorem fields_bit (w k : ℕ) (f : ℕ → ℕ) (small : ∀ j, f j < 2^w)
    (j r : ℕ) (hr : r<w) :
    (fields w k f).testBit (w*j+r) = (decide (j<k) && (f j).testBit r) := by
  induction k generalizing j f with
  | zero => simp [fields]
  | succ k ih =>
    rw [fields,Nat.testBit_two_pow_mul_add _ (small 0)]
    cases j with
    | zero => simp [hr]
    | succ j =>
      rw [show w*(j+1)+r=w*j+r+w by ring,if_neg (by omega),Nat.add_sub_cancel]
      simpa using ih (fun a => f (a+1)) (fun a => small (a+1)) j

private theorem fields_const (w k u : ℕ) :
    fields w k (fun _ => u) = u*multiplesMask w k := by
  induction k with
  | zero => simp [fields,multiplesMask]
  | succ k ih => rw [fields,ih,multiplesMask]; ring

private theorem fields_plus (w k : ℕ) (a b : ℕ→ℕ) :
    fields w k a + fields w k b = fields w k (fun j => a j+b j) := by
  simp only [fields_sum, Nat.add_mul,Finset.sum_add_distrib]

private def count (s n j : ℕ) := ((range s).filter (fun r => n.testBit (s*j+r))).card

private theorem packed_fields (s k n : ℕ) (hs : 0<s) :
    packedClasses s k n = fields s k (count s n) := by
  rw [fields_sum]
  exact packedClasses_eq s k n hs

private theorem count_lt (s n j : ℕ) : count s n j<2^s :=
  (card_filter_le ..).trans_lt (by simpa only [card_range] using Nat.lt_two_pow_self (n:=s))

private theorem count_join (s n j : ℕ) :
    count s n (2*j) + count s n (2*j+1) = count (2*s) n j := by
  have eq := Finset.sum_range_add
    (fun r => if n.testBit (2*s*j+r) then (1:ℕ) else 0) s s
  rw [show s+s=2*s by omega] at eq
  unfold count
  simp only [show ∀ i, s*(2*j)+i=2*s*j+i by intro i; ring,
    show ∀ i, s*(2*j+1)+i=2*s*j+(s+i) by intro i; ring]
  simpa only [Finset.sum_boole, Nat.cast_id] using eq.symm

/- Select the even or odd digits and unscramble them into double-width fields. -/
private theorem half_fields (s k h : ℕ) (hs : 0<s) (hh : h<2) (f : ℕ→ℕ)
    (small : ∀ i, f i<2^s) :
    ((fields s (2*k) f >>> (s*h)) &&& fields (2*s) k (fun _ => 2^s-1)) =
      fields (2*s) k (fun j => f (2*j+h)) := by
  have le : 2^s ≤ 2^(2*s) := Nat.pow_le_pow_right (by decide) (by omega)
  have msmall (i : ℕ) : 2^s-1 < 2^(2*s) := by have := Nat.two_pow_pos s; omega
  apply Nat.eq_of_testBit_eq
  intro i
  let j:=i/(2*s)
  let r:=i%(2*s)
  have hr : r<2*s := Nat.mod_lt _ (by omega)
  have form : i=(2*s)*j+r := (Nat.div_add_mod _ _).symm
  rw [form,Nat.testBit_and,Nat.testBit_shiftRight,fields_bit _ _ _ msmall _ _ hr,
    fields_bit _ _ _ (fun j => (small (2*j+h)).trans_le le) _ _ hr,
    Nat.testBit_two_pow_sub_one]
  by_cases inside : j<k
  · by_cases low : r<s
    · rw [show s*h + (2*s*j+r)=s*(2*j+h)+r by ring,fields_bit _ _ _ small _ _ low]
      have idx : 2*j+h<2*k := by omega
      simp [inside,low,idx]
    · have big : f (2*j+h)<2^r := (small _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      simp [inside,low,Nat.testBit_lt_two_pow big]
  · simp [inside]

private def stripes (s k : ℕ) := (2^s-1)*((2^(2*s*k)-1)/(2^(2*s)-1))

private theorem packed_join (s k n : ℕ) (hs : 0<s) :
    let v := packedClasses s (2*k) n
    (v &&& stripes s k) + ((v >>> s) &&& stripes s k) = packedClasses (2*s) k n := by
  dsimp only
  rw [packed_fields s (2*k) n hs, packed_fields (2*s) k n (by omega)]
  have mask : stripes s k = fields (2*s) k (fun _ => 2^s-1) := by
    rw [fields_const,multiplesMask_fast (by omega)]
    rfl
  rw [mask]
  have lo := half_fields s k 0 hs (by decide) (count s n) (count_lt s n)
  have hi := half_fields s k 1 hs (by decide) (count s n) (count_lt s n)
  simp only [Nat.mul_zero,Nat.shiftRight_zero,Nat.add_zero,Nat.mul_one] at lo hi
  rw [lo,hi,fields_plus]
  exact congrArg (fields (2*s) k) (funext (count_join s n))

/- A pair of neighboring fields is collapsed into their sum. -/
def combine (s mask v : ℕ) := (v &&& mask) + ((v >>> s) &&& mask)

def maskAt (s : ℕ) :=
  ((1 <<< s)-1)*(((1 <<< 65536)-1)/((1 <<< (2*s))-1))

theorem combine_at (s k n : ℕ) (hs : 0<s) (fills : 2*s*k=65536) :
    combine s (maskAt s) (packedClasses s (2*k) n) = packedClasses (2*s) k n := by
  have mask : maskAt s = stripes s k := by simp only [maskAt,stripes,Nat.one_shiftLeft,fills]
  rw [mask, combine]
  exact packed_join s k n hs

theorem one_fields (k w : ℕ) :
    packedClasses 1 k w = w &&& ((1 <<< k)-1) := by
  simp [packedClasses,Nat.one_shiftLeft]

end WordPop
open WordPop

private def swarM1 : {v : ℕ // maskAt 1=v} := ⟨_,by conv => lhs; whnf⟩
private def swarM2 : {v : ℕ // maskAt 2=v} := ⟨_,by conv => lhs; whnf⟩
private def swarM4 : {v : ℕ // maskAt 4=v} := ⟨_,by conv => lhs; whnf⟩
private def swarM8 : {v : ℕ // maskAt 8=v} := ⟨_,by conv => lhs; whnf⟩
private def swarM16 : {v : ℕ // maskAt 16=v} := ⟨_,by conv => lhs; whnf⟩

/- Five parallel additions compute a Hamming weight in every 32-bit field. -/
def fastPackedClasses (w : ℕ) : ℕ :=
  let v1 := combine 1 swarM1.val (w &&& ((1 <<< 65536)-1))
  let v2 := combine 2 swarM2.val v1
  let v4 := combine 4 swarM4.val v2
  let v8 := combine 8 swarM8.val v4
  combine 16 swarM16.val v8

theorem fastPackedClasses_eq (w : ℕ) :
    fastPackedClasses w = packedClasses 32 2048 w := by
  simp only [fastPackedClasses,← swarM1.property,← swarM2.property,← swarM4.property,
    ← swarM8.property,← swarM16.property,← one_fields,
    combine_at 1 32768 w (by decide) (by decide),
    combine_at 2 16384 w (by decide) (by decide),combine_at 4 8192 w (by decide) (by decide),
    combine_at 8 4096 w (by decide) (by decide),combine_at 16 2048 w (by decide) (by decide)]

namespace WordPop

/- The final incomplete field of a rank query has at most 31 bits. -/
def smallPop (w : ℕ) : ℕ :=
  let v := combine 1 0x55555555 w
  let v := combine 2 0x33333333 v
  let v := combine 4 0x0f0f0f0f v
  let v := combine 8 0x00ff00ff v
  combine 16 0x0000ffff v

private theorem small_join (s k m n : ℕ) (hs : 0<s) (hm : stripes s k=m) :
    combine s m (packedClasses s (2*k) n) = packedClasses (2*s) k n := by
  subst m
  exact packed_join s k n hs

theorem smallPop_spec (w : ℕ) (hw : w<2^32) : smallPop w = GlobalRank.pop64 w := by
  have h₀ : packedClasses 1 32 w=w := by
    rw [one_fields,Nat.one_shiftLeft,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt hw]
  have h₁ : combine 1 0x55555555 w=packedClasses 2 16 w :=
    (congrArg (combine 1 0x55555555) h₀.symm).trans (small_join 1 16 _ w (by decide) (by decide))
  have h₂ : combine 2 0x33333333 (packedClasses 2 16 w)=packedClasses 4 8 w :=
    small_join 2 8 _ w (by decide) (by decide)
  have h₄ : combine 4 0x0f0f0f0f (packedClasses 4 8 w)=packedClasses 8 4 w :=
    small_join 4 4 _ w (by decide) (by decide)
  have h₈ : combine 8 0x00ff00ff (packedClasses 8 4 w)=packedClasses 16 2 w :=
    small_join 8 2 _ w (by decide) (by decide)
  have h₁₆ : combine 16 0xffff (packedClasses 16 2 w)=packedClasses 32 1 w :=
    small_join 16 1 _ w (by decide) (by decide)
  rw [smallPop,h₁,h₂,h₄,h₈,h₁₆,packed_fields 32 1 w (by decide),
    GlobalRank.pop64_spec w (hw.trans_le (by decide))]
  simp only [fields,count,Nat.mul_zero,Nat.zero_add]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_range]
  refine ⟨fun h => ⟨by omega,h.2⟩,fun h => ⟨?_,h.2⟩⟩
  by_contra! large
  have zero : w.testBit i=false :=
    Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right (by decide) large))
  simp [zero] at h

end WordPop

/- Look up the prefix with a dynamically shifted mask and a 32-bit tail count. -/
def fastPackedRank (word packed length : ℕ) : ℕ :=
  let start := 32*(length/32)
  (packed &&& ((1 <<< start)-1)) % 0xffffffff +
    WordPop.smallPop ((word >>> start) &&& ((1 <<< (length%32))-1))

theorem fastPackedRank_eq (word packed length : ℕ) :
    fastPackedRank word packed length = packedRank word packed length := by
  simp only [fastPackedRank,packedRank,Nat.one_shiftLeft,Nat.and_two_pow_sub_one_eq_mod]
  apply congrArg (fun a : ℕ => packed % 2^(32*(length/32)) % 0xffffffff + a)
  apply WordPop.smallPop_spec
  exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end Astra247824

/- Window the signed denominator masks before reading any prefix ranks.
A zero denominator word ends its loop immediately. -/
namespace Astra247824.HardTail.Cells
open Finset Leaves ArithmeticFunction

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def readBits (f : ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | n+1, first, word => if word=0 then 0 else
      (if word.testBit 0 then f first else 0) + readBits f n (first+1) (word >>> 1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem readBits_eq (f : ℕ → ℤ) (n first word : ℕ) :
    readBits f n first word = ∑ i ∈ range n, if word.testBit i then f (first+i) else 0 := by
  induction n generalizing first word with
  | zero => simp [readBits]
  | succ n ih =>
    rw [readBits]
    by_cases zero : word=0
    · simp [zero]
    · rw [if_neg zero,ih,sum_range_succ']
      simp only [Nat.add_zero,Nat.testBit_shiftRight]
      rw [add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      simp only [Nat.add_assoc,Nat.add_comm 1 i]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def window (word first n : ℕ) := (word >>> first) % 2^n

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem readWindow (word first n : ℕ) (f : ℕ → ℤ) :
    readBits f n first (window word first n) =
      ∑ d ∈ Ico first (first+n), if word.testBit d then f d else 0 := by
  rw [readBits_eq,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
  apply sum_congr rfl
  intro i hi
  simp only [window,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,decide_eq_true (mem_range.mp hi),Bool.true_and]

/- The public API for the table of positive and negative denominator weights. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def GoodWords (words : ℕ → ℕ × ℕ) := ∀ {p d : ℕ}, p.Prime → 23 < p → p ≤ 3006 → p < d → d ≤ Y →
  ((if (words p).1.testBit d then (1:ℤ) else 0) - (if (words p).2.testBit d then (1:ℤ) else 0)) =
  (if p < d.minFac then -moebius d else 0)

/- Build the rank summary only after at least one denominator survives both bounds. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem read_zero_for_skip (f : ℕ → ℤ) (n first : Nat) : readBits f n first 0 = 0 := by
  cases n <;> simp [readBits]

/- Low zero bits can be discarded together before visiting the next denominator. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem read_skip (f : ℕ → ℤ) (k n first w : Nat)
    (low : ∀ i < k, w.testBit i = false) :
    readBits f (k+n) first w = readBits f n (first+k) (w >>> k) := by
  induction k generalizing first w with
  | zero => simp
  | succ k ih =>
    rw [show k+1+n = (k+n)+1 by omega, readBits]
    by_cases z : w=0
    · simp [z, read_zero_for_skip]
    · rw [if_neg z, low 0 (by omega)]
      simp only [Bool.false_eq_true, if_false, Int.zero_add]
      have next (i : Nat) (hi : i<k) : (w >>> 1).testBit i=false := by
        rw [Nat.testBit_shiftRight]
        exact low (1+i) (by omega)
      rw [ih (first+1) (w >>> 1) next]
      simp only [← Nat.shiftRight_add]
      rw [show first+1+k = first+(k+1) by omega, show 1+k = k+1 by omega]

/- The checked remainder makes the skip valid for every candidate position. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def sparseBits (f : ℕ → ℤ) : Nat → Nat → Nat → ℕ → ℤ
  | 0, _, _, _ => 0
  | fuel+1, n, first, w =>
    if w=0 then 0 else
      let k := min n ((w ^^^ (w-1)).log2)
      if w % (1 <<< k) = 0 then
        if n ≤ k then 0 else
          let tail := w >>> k
          (if tail.testBit 0 then f (first+k) else 0) +
            sparseBits f fuel (n-(k+1)) (first+k+1) (tail >>> 1)
      else readBits f n first w

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem sparseBits_eq (f : ℕ → ℤ) (fuel n first w : Nat) (enough : n ≤ fuel) :
    sparseBits f fuel n first w = readBits f n first w := by
  induction fuel generalizing n first w with
  | zero =>
    have : n=0 := by omega
    simp [this,sparseBits,readBits]
  | succ fuel ih =>
    rw [sparseBits]
    by_cases z : w=0
    · simp [z,read_zero_for_skip]
    · rw [if_neg z]
      let k := min n ((w ^^^ (w-1)).log2)
      change (if w % (1 <<< k) = 0 then _ else _) = _
      split
      next rem =>
        have kn : k≤n := Nat.min_le_left ..
        have bits (i : Nat) (hi : i<k) : w.testBit i = false := by
          have h := congrArg (fun m : Nat => m.testBit i) rem
          simpa [Nat.one_shiftLeft, Nat.testBit_mod_two_pow, hi] using h
        have skipped := read_skip f k (n-k) first w bits
        rw [Nat.add_sub_of_le kn] at skipped
        rw [skipped]
        split
        next done =>
          have : n-k=0 := by omega
          simp [this,readBits]
        next next =>
          have nn : n-k = (n-(k+1))+1 := by omega
          dsimp only
          change (if (w >>> k).testBit 0 then f (first+k) else 0) +
            sparseBits f fuel (n-(k+1)) (first+k+1) (w >>> k >>> 1) = _
          rw [nn,readBits,ih (n-(k+1)) _ _ (by omega)]
          by_cases zero : w >>> k=0
          · simp [zero,read_zero_for_skip]
          · rw [if_neg zero]
      next _ => rfl


namespace Jump
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def firstSet (w : Nat) := (w ^^^ (w-1)).log2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem xor_odd (w : Nat) (nonzero : w≠0) : (w ^^^ (w-1))%2=1 := by
  apply Nat.xor_mod_two_eq_one.mpr
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem firstSet_correct (w : Nat) (nonzero : w≠0) :
    (∀ i < firstSet w, w.testBit i=false) ∧ w.testBit (firstSet w)=true := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases odd : w%2=1
    · have same : w/2=(w-1)/2 := by omega
      have div : (w ^^^ (w-1))/2=0 := by rw [Nat.xor_div_two,← same,Nat.xor_self]
      have bit := xor_odd w nonzero
      have one : (w ^^^ (w-1))=1 := by omega
      have first : firstSet w=0 := by unfold firstSet; rw [one]; rfl
      rw [first]
      exact ⟨fun i h => (Nat.not_lt_zero i h).elim, Nat.mod_two_eq_one_iff_testBit_zero.mp odd⟩
    · have wpos : 2≤w := by omega
      have xpositive : w/2≠0 := by omega
      obtain ⟨before,atBit⟩ := ih (w/2) (Nat.div_lt_self (by omega) (by decide)) xpositive
      have lower := xor_odd (w/2) xpositive
      have div : (w ^^^ (w-1))/2 = (w/2 ^^^ (w/2-1)) := by
        rw [Nat.xor_div_two, show (w-1)/2=w/2-1 by omega]
      have large : 2 ≤ w ^^^ (w-1) := by omega
      have next : firstSet w = firstSet (w/2)+1 := by
        unfold firstSet
        rw [Nat.log2_def (w ^^^ (w-1)),if_pos large,div]
      rw [next]
      constructor
      · intro i hi
        cases i with
        | zero => cases bit : w.testBit 0 <;> simp_all
        | succ i => rw [Nat.testBit_succ]; exact before i (by omega)
      · rw [Nat.testBit_succ]; exact atBit

/- Visit one surviving denominator on each recursive call. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def jumpBits (f : Nat → Int) : Nat → Nat → Nat → Int
  | 0,_,_ => 0
  | fuel+1, first, w => if w=0 then 0 else
      let k := firstSet w
      f (first+k) + jumpBits f fuel (first+k+1) (w >>> (k+1))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem zero_lower (w k : Nat) (low : ∀ i<k, w.testBit i=false) : w%(1<<<k)=0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i<k
  · simp [Nat.one_shiftLeft,Nat.testBit_mod_two_pow,inside,low i inside]
  · simp [Nat.one_shiftLeft,Nat.testBit_mod_two_pow,inside]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem jump_eq (f : Nat → Int) (fuel n first w : Nat) (short : w<2^n) :
    jumpBits f fuel first w = sparseBits f fuel n first w := by
  induction fuel generalizing n first w with
  | zero => rfl
  | succ fuel ih =>
    by_cases z : w=0
    · simp [jumpBits,sparseBits,z]
    · have ⟨low,bit⟩ := firstSet_correct w z
      let k := firstSet w
      have kn : k<n := by
        by_cases within : k<n
        · exact within
        have bound : w<2^k := Nat.lt_of_lt_of_le short (Nat.pow_le_pow_right (by decide) (by omega))
        have falseBit := Nat.testBit_lt_two_pow bound
        change w.testBit k=true at bit
        simp [falseBit] at bit
      have k_eq : min n ((w ^^^ (w-1)).log2) = k := Nat.min_eq_right (Nat.le_of_lt kn)
      have lowMod : w%(1<<<k)=0 := zero_lower w k low
      have atZero : (w>>>k).testBit 0=true := by
        simpa [Nat.testBit_shiftRight] using bit
      have fits : (w >>> (k+1))<2^(n-(k+1)) := by
        rw [Nat.shiftRight_eq_div_pow]
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        rwa [← Nat.pow_add,Nat.sub_add_cancel (by omega)]
      rw [jumpBits, sparseBits,if_neg z,if_neg z]
      dsimp only
      rw [k_eq,if_pos lowMod,if_neg (by omega : ¬ n≤k),atZero]
      simp only [if_true]
      rw [← Nat.shiftRight_add,ih _ _ _ fits]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem jumpWindow (f : Nat → Int) (n first word : Nat) :
    jumpBits f n first (window word first n) = readBits f n first (window word first n) :=
  (jump_eq _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos n))).trans
    (sparseBits_eq _ _ _ _ _ (Nat.le_refl _))


end Jump

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def eval (words : ℕ → ℕ × ℕ) (b p word : ℕ) : ℤ :=
  let first := queryLow p b + 1
  let n := queryHigh p b + 1 - first
  if n=0 then 0 else
    let pos := window (words p).1 first n
    let neg := window (words p).2 first n
    if pos=0 ∧ neg=0 then 0 else
      let summary := fastPackedClasses word
      let rank := fun d => (fastPackedRank word summary (X/(d*p)%W+1) : ℤ)
      Jump.jumpBits rank n first pos - Jump.jumpBits rank n first neg

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem read_zero (f : ℕ → ℤ) (n first : ℕ) : readBits f n first 0=0 := by
  cases n <;> simp [readBits]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem eval_eq (words : ℕ → ℕ × ℕ) (ok : GoodWords words) (b p word : ℕ)
    (pp : p.Prime) (large : 23 < p) (cap : p ≤ 3006) : eval words b p word=cellValue p b word := by
  let first := queryLow p b+1
  let n := queryHigh p b+1-first
  let rank := fun d => (packedRank word (packedClasses 32 2048 word) (X/(d*p)%W+1) : ℤ)
  have same : Ico first (first+n) = Ioc (queryLow p b) (queryHigh p b) := by
    ext i
    simp only [mem_Ico,mem_Ioc,first,n]; omega
  have tab : eval words b p word =
      readBits rank n first (window (words p).1 first n) - readBits rank n first (window (words p).2 first n) := by
    change (if n=0 then 0 else if window (words p).1 first n=0 ∧ window (words p).2 first n=0 then 0 else _) = _
    by_cases empty : n=0
    · simp [empty,readBits]
    · rw [if_neg empty]
      split
      next h => simp only [h.1,h.2,read_zero,sub_zero]
      next _ => simp only [Jump.jumpWindow,fastPackedRank_eq,fastPackedClasses_eq,rank,n,first]
  rw [tab,readWindow,readWindow,same,←sum_sub_distrib]
  unfold cellValue queryDenoms
  rw [sum_filter]
  apply sum_congr rfl
  intro d hd
  obtain ⟨lo,hi⟩ := mem_Ioc.mp hd
  have lower : p < d := (le_trans (le_max_left p (Y/p)) (le_max_left _ _)).trans_lt lo
  have upper : d ≤ Y := by
    unfold queryHigh at hi
    split at hi
    · exact hi.trans (min_le_left ..)
    · exact (hi.trans (min_le_left ..)).trans (min_le_left ..)
  have sign := ok pp large cap lower upper
  have mul := congrArg (fun z : ℤ => z*rank d) sign
  simp only [sub_mul,ite_mul,one_mul,zero_mul] at mul
  rw [mul]
  by_cases sf : Squarefree d
  · simp only [sf,true_and,rank]
  · simp only [sf,false_and,moebius_eq_zero_of_not_squarefree sf,neg_zero,zero_mul,ite_self]

end Astra247824.HardTail.Cells

namespace Astra247824.HardTail
open ArithmeticFunction

/- The bits of a denominator index select its prime status and, for eligible
squarefree semiprimes, the eight bits of its smaller prime factor. The kernel
checks these tables against the Möbius function and minimum prime factor. -/

private def primeWord : ℕ := 0xa08000000000000008028200000808008020000020008000820020020000808000200020008020000008800a00200008200800200800820200820208000028000000008820028020200000220800208000808200808020a20208200800020a00000008000020020a00200000200000200808800208a20808220000028820800820008020020808000808200a00000200008008a00200220828020020000808000000200208028020000800008a20008000a00200a20820008000808220808000800a08000000220200000208028000020200800000008200200808820008220a08220008000000208800028208000800800800200800000028008028200000208020200000000800020020820008028820200a00208a00020020a00800220000000220000208808000820800020000200200200820800000820008800800228200208820020008000808808008000000200a20000000000000a00800020020808200008000800a00800808208800800800000228800000000800000220808000000000000208200000200220800020000220020208028000028800800820800000800000a08000220000208808000200020200000020008820208200828028200000808008020200200020808020800000808808000000808800800000200208008020000200a08800000000200808800008020020008028808000a00008220020200000000008028228020200808020000a20000820008208820200800000008a00008800000200020800820000200a20008008000208200800820020000800808000800028020208028808200020a00028008020000a08020000028220008000000000200000000028228000800000000200020800008000228220008800820200200000a08008000220208200800220000000820000000800200020808000000800228800008820800000000008020200808020208000800028008000a00000000800000020000828000000820208020008008000a00828820028020200208820220800008000820000800200200008020a20000a00020228000000220000200800008200028020200800800008000820000200800000220200800028200820000820000008800a08820028008020800200800200200200028828008200200800020220020808208000200820200000808008800808808020028800000220008228020800020000000000208020000200a00000820808200020208008020020020200008800000200800208000028020008020820000020000228808200820208008000200800800a00008020800800a08000020a20000008008208000a00000000000020800000000000020008228000220000008228820028000800000020028020008800820200200008020008008820800008028008020800000820000200000008008220200200208808020a00200828000008800000000020000a00200800008200020008208000028a00000800800000200008a00808020200008020808208000a00008000208800a08000000020820000828028008800a00200008020200008000020028200800200808200a20008020828200000800228000000800800a00820028800000000000000220000828008000020000000820000220808008000220000808208000028000a00208000228020a00800020200800000800000008220208a20028028220208000800220200008020808020220000000800220800800200008228800a00208020028000000000800000800808808028000200a00000008208000808028000220020208020008208800a00200028200020a00000800020000008828000000a20208808000020000000a20800208000000020800200200a08000808220a00000228000008820800800800000a00208028020000220a08820020008a00208a00000000220800220000200800a08020008000a00000a00008020820208a08000028000208008020200820000000000008000808020008028000000200008200000a00008020028a00000800800008820208000800008200008020800008a00800228000020220200000000000000000228808000020000220828008000000208808228020808800000220a20000828808000a00000008028020800800820008200000008208000020220800008000200200a00828028020020208000020200820000000800208820200208020020820800000000200020000a20008020020200228000028000200008800000800a00000800008200008820800200000a00820020000800808200820020200000a20008220820a00008008008000200028000020800000800800008220000000028208800800220008000800200000028200200008200000000800a08000020220000800800820228000000208800000200008020000200820208008028028800008000808208000808200800020000808008020028200800820800208020a08000020000020008800000208a20200000008000200200020820020200000808808000820000220800220000800828000020800808200800020a20208008828008820800828008028220000220008200020008000808220000a08020800000000a00000008028020208a00000000000200808020000a00008008000000800a00a00820020020800008808000220008000820208a00000a00020200800000008800008820208828008208800a08a20000000220a00020000208000800208000000a00000008028028000200000828000020200208800028020000000820000020200000008000a20800820028000000800208008000000008000800028800800220828000800800208000208200000828800008200008028028000a00200820020200200008200008000020a08228028208a00200000820208000000208000200220000800000200220200800008020020808200808208000800200808000220200220000008a00a00200800020800208208020200200000828808000800000020020020220008a00020020000808828008200800200020800028200000800028200000808800820200020008020008208020008820020020a00208a00020000220008000000000000a08220808000800a00008000208020208800020028a00000000020208820200800000020800a08020800008220800200800200020000228000200000200a08800200800008a00800020020000808820000200200820020008800200020000020020808208008000000808008000200000800008800208020200800020220000008800028208000800828008000020200200000000200000008808020800008200028020000800220020228820808208020020800208800820200220800200000020020a00820808220020000028808200200200020820208a00000800000028020a08000000228800208820020008a20200a08000020020000020008008000800200008000000a00200008208200800228008020000800000800020a20200020808000800800200008008200808a20028028220808020000200a00008200020008200000208028200000000208800008820200008028008220200a08008020000808a00028200000000028800020a00800008020000a00200020820200000200208020028000208000000008800808a28008008000200000000220000800a20800220800a00028008208800800a08800200820800200020000820200008000200200808808028000220008800800208020800a00800200200008020020028000000228028028020208a00000020a20008828820008000000020008008220808a00000008200008a20000000820200000800008200800028808020820208800020008200200000828000000808a28020000a00008800808020200008a00808200020200000000028000200028008228800800a00800200200008000028008000800820000000800a08020020028000008a00000000a00800008808220000200a20820208800000200800020200200028008000200008220020028800208220820020000808008800020a00800228008200a00200200808200000a00000820200a00000820020200020008828008008020200a00820000200000000000020820008208008200a00800000820020820a08200820228a20008008828200000000020008020200200020808020020800828800000a00008200028000200000000828220000800208000220200000820008008000000a28008000000200800008000000008220800200020208008008200200800808020000020000200000208800000020028000a20008020020000220808820800200220000808800200200200028820028000200228000220820800808020020000208028828000020200200028028a00000020000028220800a00008020a00a08008020000800800a00800008000a08000020028020200020800000a00200a00000008800200a00028220000800800008020020a08208800020800800a00020228820000808020208220000828000000020000808000028800a08000808000020008200808200020000020820228200800020828000800008208820000a00208808000000800a08008000008000008800820020000008828000200220a00028008008800000020820208000200800000208220000028800208220800000020020a00200820008000200000020800220000a08200000228800000000028008000808208800228a20000020000008200800028008000020008820820028220000800000000820208208800208200200a28800000000008808820028a00200800820000a00200808020008000800220000208200808800800200200808220028020000a00820808028020a08800020208020000820800200200200a08020008200808220020200000800220000000800200208808020800000208808028000808008820200020008808808208220808220008000800200220008228200000028000000a20a08220008000800200800020028020808808820028000200000820008a00008020020000000a08000020008020000220008220800000000800008a00800208000220000a00a00000008800000028020208a00008a20008000200a00000808020200008a08000020a00a00228828020000200020808200020800200800200020008020008008020208208020000220800a00020008000000a08800220020800000808020200200a00000008820808808800008200208820000000800208220000028a00008820808200200008a08808220000000020020020a00200808020000820008800020200820200008008208220000828020020820200020828008020808208808200020800220020220200800a20000008800208000020020220208028028008000808200000000a20208000008228220000028000020a20000008800008200a00820028208800208200800008800000828820208200208a00000000800800a00028020220000200000200220000220808000000a00000808000820a08008800008820008008008200800200028000020220800800808200220808800000200020000228028020000800a20000208800a00a00800008000008020808200020200a00000020800a08000828208020800000008020200800020008220800a00008800008820800808800208220200000808000000a00020028008020008a20000228000000808000020020008228020200a00200028808208800008008000200220208808028200000808828008028200000a00000028000000020800020200a08000820008800800a08008220020808008820028000208820028000020200a00020020800a08820020008000000008808200200800208008208a00000a28028200820800208000020a20008808000200a20000200028008200208800820200220800220800020800800000808020a00200028828000000a08008020220800000020800008a00200a08028008800008800020208220800820808220220208000820028800200a00020200800008a00820200200000000820008800a08800000028020208020000020020800228800220800008228028020000800808820008000008208020228200200820008000020a00020000000800a00220808008200008a20800200200208200000220000000a20020008820008808820220000208800020008800a08220028028220208200808028220000a08000200020800020000020000a00028020028020008000000208820200828800208020000808000028200208000008020020008800808200220808208828028000000208808000800a08200020228800008028028000a00000220008020a00a00820028200020000800808000220a08028800020200000008020220000a00000820000020200820828200820208208028008020a08200800020220808a00000200800808028020200200a00820800208820200008800008200000020008008800008200028028220a08800820208200808800000020a20000208020220800200a28828000800000008020220820000008828008a00008a08000020a20800a20808208200000008800200800208200028200200000228800020020200808800208000000820828008220000808008000a00a08820800228020808228008020800200208020000000800220028228800000808000220a00008008008200820a08a00020000820808000820028000008a20800200a00008208820000a00200208000200820200a00800000020208028028200a00a00a08020000020000a20008228000800828008200020a00000828208a00200000800008800a08a08800020220008028800200a00008220008028200000820808020220800228008000820808220800200a00800a00828228020800808000028a20200020000208000a00028028008800a08820828000000800a28000020220208008820028800000200028020000208800820020220008808028000000a08220008008020208200808000220808220008000a20a00200800220200a00828808228820808a00800200220200028008000020a08808020000800000220808008220008208008220a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac

private def plane : ℕ → ℕ
  | 0 => 0x800020a20208000800000000200820008028800200020000200000000200008000000000208020000000000808000020000008008000008000000800800200220a00008000008020800800020000200000820000000000000028020000000a00020808208800008000800020200000000008000000000008020000200000200000200000000800000000020a00000820200000000008000208000a00000820000800000000008000020000008020020000000000000000020000008000020200000008800008000000820000228000000008800220820008000000000800000000020008800800220800000200000028000020000000200800000000200800808020020a08208000200000000000008008000000000008000020000000008008000800020000220000008008028028000800000020200000a00200000000020000008000000000200220020008a00000000000220220008028008000000200000820200200000200020000000008000020000200000820008208800200028020020a20800800808008000000a08808000000000000020200200000208020008020000000020000800000020028008800800228000020000000000000200000808000000200020800208000208000000020000028000000200000008000000020800000020000220000008000200220820008000000800000000020a00000000020800a00200000000800808000800208000000008000000200000028008000020200000028020000008200000000000800200820020000200200800208000200008020000000000800000000a00000800000000000000000828000000000208800020820800220000000800200a28800000800000800800000000000020008000820008000020000000800820020008200008200808020200000000020200a00200000008020000200208000220200008000000000220008800020000020a00800000208200808000008220000000200800000800000200000000000008000000000200200800000000000008828000000000808020808000000800000800000200a00008000008000000228000228000200000000208000000000800000200a08200000000020000000000220000008028000000000800200000020800000020008000000000800820020000008008000000220000200008000200008000000000000000200808000a00800008808020000800000020008000000800800000000008800020208000208800020000800200a00008200000800800000000000000220828008000200000020000000008000020208000000820800000a00008020000028200200220808000200800800008000200800000000000200000008008000000200200000020800200000020200000008200000000a00200a00008020020008800000000820000000000000000000000828200000800a00800208000008020820008000200020020000000808220000008020000000000200020a00008020020000000020820020000000a08000208000000000000000000000028000008020000820808200000008000000000000800208000000200000000800220000208000000000220008028828000000208200000028800200220000008000000800808000800000020020000a00000820000000000008008000008220200020828200000000000000000000800800000000000000808000000800008028000000200200000820000000008000000000820000808008208220000200000020020000800800020200000000800000800000200020000000000028800000000000a08020200800200000008008000000200000000800808000020020020808008008020000000200020000000800000008000000200200000028020000000008008000000000008000000800020800208000000808000020000000008000000000000008820200000000000800200820000000008000200a00208028000820000a00020200000800800000020a20000020800000000200020008000000800008020220000200008020200000200800000000000008a20008020020808000000200800800000000220200200800020000800000000020000000200000000200000800800000008200208200020008020000020808000000200200800008800000200800000000000008000000000208828020000000808020000000000208800828008200000008000000800000000800200a00800800000020020000200020200000000000028008200008200000008200000020008008020008000800000200008000800220000800000808208020000008020200000000028000000020000800000008020000800000028020000820800000220000208008000000000028000000000008800020000800200800808000200000020000000000200220000020200000800000200000000000008200000000208000020800000808000200800200000828000000800a28020028000008800000008000800200000000200200008028000800000200020200000000000000208000000000000000200008000000000000a00000000028000800820000000a20000200020000a00000208020000000000000020008a00000020808008000000220020000220008000008200000000000000220800000208008000000000020000008020800200000000200000000800000020000000008008000000800820020200000820000220000808020000000000000a08000200000800000000200800208028008000800808208000000000008200000220200000820800020200000020028000200200000000000000208800800020020208000000000000200800000028020000200800000020800820000200800000000000000000800800000020820008800000008800200008800000000808008020008a00000020000000000008800000020000800008820020000000020008008000000800800020020008000020200020208208000000800200000008000020000200000000200000208000200800000028800008020200200000000000200800020000200800200000000000800020808008000000028008020220000008000028000000220808000000800008000000020008028000000200000200008008000000800020200000000000008000800208000028020000800000020020000a00000020008a00000000008000800800200008000000808000820008000000000000200220000220020020200200820008000800808000800008220000020000000020008000000008200000820800028000000220000000220200000000000a00000808008000000000000800208000000000008000000008008028008800000000000000200008800000000020800000000000000200208820000000000a08020000000000008800000000000020020000200200800800220000008008800200a20008000800020800000000020008800200000000200000008000000008200200800000000820000000000200000000808800020000a00000800020800200820000020820200000000000000000020000200800008000020000820000000000000220000a00000000020008020808228000000800000008000808000800000220000808800200000200000020000020008020808000220008000000000000000000020000000000000008008000000808000020200000000008008820000000000020800200200000000200000028008000000800200800200000a00000000000800000000000200000200000008200020208000020020000200000020220000800008000220000800028008000000200000020208000000000800200800000800000200220000000000028000800000020000000000000000020800000228828000800000200000000020000008020008000000808000200820200208000028020000000000200020800020808200020200020000000200000008000000000008808000000020008800820000800800000000000000800000008208200000200000000020008000000008000800820000020020008808000008020208000000008a00200000000020000000020000208000800a08000000000000000020020000200808000200000000008000000000000000000008000800a00000008800800200000000200008000008020020000020800008000200820000000000208800800008800008008020000000008000020000220800200820208020000000008000200000200820020800000020008000800800808000000000200800000208000a00200000008800000200008028000808000000020000008000000000a00000000800000000208200000008820000000000200800800800000000000008a00028000000000000800200000000000800220200000000028200000000000800200200008008020000000800020008000220000020800000020008028000200000000020000208200000000008000000008000000000000000000808008a00208000008000200000a00000000200800028000000000808200000000000200800000020020000000000020020000020800000020000200028020200a00000000008020000200000020000000200000200000a00808000000800800200000000800208800020000000208008000000000808000000020020000a08008000a00000020008000000800208800000020200000000000000008800028200000200000000028800800000000000000800220008200000800000028000000000000020008800000200000000000000008000200020008220008020020008000020020000000200000000820000000000008800000008000200000000008800020200200000008000800800020000000020200000000028000008000808000200000000020200200000820000200820200200000020800000000000000000000808020020200000800800000020000000008000000000000800008000800220000200000200000000200200008828000000020200808008000020000020808200000000008800000220200008020020000000000008000820000000800220000008800008000000000000020008820000200020000000800000800200000008000000008000000008020020800200808020000000200008000200800000800008000800000020000200200000020000000a00208000020000000800020828200000000200000000000000000020008200800008008000020200000000000000800020000000020800008008208000000200000200000800200000028000000800800000800200000008008000000000000200000000000000020000200008000000800000008820020000000a00800000800000000800000000000028000020000000a00800000000808800008000000800220000200000000000000020000800800000200020000000008000020000028000020200200000000000000008828008000800008008020208800000200020008000000000020000000000020000008020800a00000008000208000000020000000020800000000208000000008000200008000000000000008020020a00200000020000200808000028000000000220000000200008800800200800008200000000200000000008020000000000000000000000820020208220000800000000200800000820000000008200008000800200000000000000800200020020000200000800008000000000800000820000000000000020000020808000200808000000200800000200000000200200020800008000000a00000000200000008800000a00000000000000200000200000220020008020000000820200000800000000000000000000000200800000200000000020820008000808800000000000800000008028000008000000000000208028000008000000200000020020000000000008020200000020000000808000000000000800220000000000000008000000000000008008200200800000800000020200000000028000000828000200000000020028000800000200008000200000800000000000a00000000200200000000008200020800000000000820000008000000800008008008008020000000000200020000000000020000800008800000a00000000808020000000200000000a00000000000000020000008000000000000800000200000800000008000200200000808208800000800000200800200000020000000008000000000200a00000020000000000a20020008000000208000020800000000000000800000020020208000000000800000000000000000008000800008000000020008000800020000008000000000000000200020208000000a20000000000000a08000008200000000000000000000820000000800000000000000000000008008020220000000000028000000200008000000800000000020820208800000000220000028000000000000000000020000000200800000000008000008000000800000000200020a00000800000200200000000200000000000028000000200000000000000808020000000000800020000000000800000000008000008200000000a00008000000000000208020000020000000000000000000000000000000020800000808008200000800000000000000200800000020000800820000200000020008000200000000008000000000000000000000200020000020000000800800000000008008000028000000000000008000008000000028a0080000002000000000000080000020000002000000000000020000820002000000002000000020000000000800080000000000080000020000020000000000000002000000000000802000020000800000000000800000000000000000800000082000080000000002000020000020000000000000820000000002000000000020080880000000000000800020000000000080020000000000000000080080000002000800000000000000000000002000800800000000002000000000000000000880000000000020000000020000000020080080000002000000080000000000000000000000000000000000800082000000000000020000802000000000000000000000002000000000000020000000000000020000000080000000080000000000000020000000000000000800000800000000000000000000000800000000000080000000000000000020000000000000020000000000000000000000000000002000000000000000800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 1 => 0x800020a20200000000000000000000000008800200020000200000000200008000000000200020000000000000000000000000000000008000000800800200000a00000000000020800800020000000000820000000000000028000000000200020000200000008000000020000000000008000000000008020000000000200000000000000000000000020200000800000000000008000000000000000800000800000000000000020000008000020000000000000000020000008000000000000008800000000000000000220000000000800020020000000000000800000000020000000000000800000200000020000000000000200800000000000800008000020008000000000000000000008000000000000008000020000000000000000800000000000000008008028008000800000020200000a00000000000000000000000000000200020020008200000000000020000000020008000000000000020200200000200000000000008000000000200000820000200000000008000000220800800808008000000208800000000000000000200000000008000008000000000020000000000020008008800000228000000000000000000000000000000000200020800208000208000000000000020000000000000008000000000800000020000200000000000200020020000000000000000000020200000000000800200000000000000000000000200000000000000000000000000008000020200000028020000008200000000000800000020020000000200000008000200000020000000000800000000200000800000000000000000800000000000000800000800000020000000000200828000000800000000800000000000000000000820008000000000000000020020000200008200008000000000000000000800200000008020000000208000220200008000000000200000800020000000a00000000008200800000000020000000000800000800000000000000000000000000000000000800000000000000008000000000008000808000000000000800000200a00008000000000000000000220000200000000200000000000000000200a08200000000020000000000200000008008000000000800200000020000000000000000000000800000020000000008000000020000200000000200000000000000000000200008000800800000008020000800000020008000000000800000000000000000008000008800000000800200200008200000000000000000000000000828000000000000000000000000000000200000000020800000a00008020000008200000000800000200000000008000200000000000000200000008008000000200200000020000000000020000000008200000000800000a00000000000008800000000000000000000000000000000020000000000a00800000000008000020008000200020020000000000020000008020000000000200000800000020000000000020800000000000a00000008000000000000000000000028000000020000020008000000000000000000000000208000000000000000800220000208000000000000008020000000000208000000028000000000000008000000800000000800000000020000200000020000000000000000000000220200020800000000000000000000000800000000000000000808000000000000020000000200000000000000000008000000000820000800008200220000000000000020000800000000200000000800000000000000000000000000028800000000000a08020200800200000000000000000000000000000808000000000000000008008020000000000020000000800000008000000000200000008020000000008008000000000000000000800020800200000000808000020000000000000000000000008020200000000000000200800000000000000200200000008000020000a00020000000800800000020020000000000000000000000008000000800008020000000200008000200000000800000000000000a20000000000008000000000800800000000020000200800020000000000000000000000200000000200000000000000008000000000020000020000020008000000000200800008000000200000000000000000000000000008808020000000800000000000000000800820000000000000000000800000000800200200000000000020000000000000200000000000000008200000200000008200000000008000000008000800000200008000800020000800000008000020000000020000000000028000000000000000000000020000000000028020000020000000220000200008000000000008000000000008000000000800000000800000200000020000000000200200000020000000800000000000000000000200000000208000020800000008000200800000000808000000800a20000028000008800000000000800200000000200200008028000800000000000200000000000000000000000000000000000000000000000000a00000000020000800000000000800000000000000200000200020000000000000020008200000000808008000000020020000020000000008200000000000000000000000008000000000000020000008000800000000000200000000000000000000000000008000000000020020200000800000020000808020000000000000a00000200000000000000200800008020000000000800208000000000000000000000200000820800000000000020008000000200000000000000200000000000000008000000000000200000000008020000200800000020000000000200800000000000000000000000000020820000800000008000200008000000000808008020000800000000000000000000800000000000800000000000000000000000000000000800000020020008000020000000208200000000000200000008000000000000000000200000000000200800000020800008000000200000000000200800000000200000200000000000000020000008000000020008020200000008000028000000020000000000000000000000000008020000000200000200000000000000800020000000000000008000800008000028000000800000000000000800000000000200000000008000800800000008000000000000820008000000000000000020000220000020200200020000000000808000800008000000000000000020000000000000000000800000020000000220000000000200000000000000000008000000000000000000208000000000008000000008008000008800000000000000200000800000000000000000000000000000008800000000000808020000000000008800000000000000020000200200000800220000008000000000a00000000000000800000000020000800200000000200000000000000008000000000000000020000000000200000000008800020000800000000020000200000000000000000000000000000000000000200800000000000000820000000000000020000a00000000020000020800220000000000000000000008000000000220000000800000000200000000000000008000008000020000000000000000000000020000000000000000008000000808000020000000000000008820000000000020800000200000000200000028000000000000000800200000200000000000000000000000000000000000008000020000000020020000000000000200000800000000200000000008008000000200000020200000000000000200800000800000000000000000000028000800000020000000000000000000800000220820000800000200000000000000008020000000000008000200000000208000028000000000000000020800020000000020200000000000000000008000000000008008000000020008000000000000000000000000000000000000200200000200000000000008000000000000800820000020000008808000000020208000000008200000000000000000000020000208000800008000000000000000020000000200800000000000000000000000000000000000008000000800000008000000000000000200008000000020020000020000008000000800000000000200800000008800000000020000000008000000000220000000820008020000000000000000000000000000800000020008000800800800000000000200800000200000a00000000008000000200000008000008000000020000000000000000800000000800000000200200000000020000000000200800800000000000000008200020000000000000800200000000000800020000000000028200000000000000000000000000020000000000020008000220000000800000000000008000200000000000000200200000000008000000000000000000000000000800008000208000008000200000000000000000000008000000000800000000000000000000000020020000000000000000000020000000000000200008020000800000000008000000200000020000000200000000000800800000000800000200000000000200000000000000008000000000000808000000020020000000008000000000020000000000800208800000020000000000000000000800008200000200000000000800000000000000000800020008200000000000028000000000000020000000000000000000000000008000200000008220000000020000000000020000000200000000000000000000008800000000000000000000000800000200200000008000800000000000000020200000000000000008000800000200000000020000200000800000200020200000000020000000000000000000000008000000000000800000000020000000000000000000000000000000800200000000000200000000000000000820000000020000808000000000000020008000000000000800000220200008020000000000000000000020000000800000000000000008000000000000020000000000000000000000800000800200000008000000008000000008000020000200000020000000200008000200000000800000000800000020000200200000020000000200000000000000000000000828200000000200000000000000000020000000800008008000000200000000000000800000000000020000008000000000000200000000000000200000020000000800000000800000000008000000000000000200000000000000000000200008000000800000000820000000000000800000800000000000000000000000000020000000000800000000808800008000000000000000200000000000000020000800000000200020000000000000020000008000020200000000000000000008020008000800000008000208800000200000000000000000000000000000000000008020800000000008000200000000020000000020800000000200000000008000200000000000000000008000000200000000020000000808000020000000000020000000000008800000200000008200000000200000000008020000000000000000000000800020000200000800000000200000000800000000000000000000800200000000000000000200020000000000000800000000000000000000020000000000000000000020008000000008000000000000000200000000000200020800008000000000000000200000000800000800000000000000200000200000020000000000000000020000000000000000000000000000000000800000200000000020020000000008800000000000000000008000000000000000000000008028000008000000200000000020000000000008000200000020000000000000000000000800220000000000000008000000000000000000000000800000800000020200000000028000000008000200000000020020000800000000008000000000800000000000000000000200200000000000200020800000000000800000008000000800000000008008000000000000000000000000000020000000000000000a00000000008020000000200000000a00000000000000020000008000000000000000000200000800000008000000200000808000000000000000200800000000000000000008000000000200a00000000000000000a00000000000000208000020800000000000000000000020020008000000000000000000000000000008000800000000000000000000800000000000000000000000000200020200000000820000000000000808000008000000000000000000000820000000000000000000000000000000000020020000000000008000000200000000000000000000000820208800000000200000028000000000000000000000000000000000000000008000000000000000000000200000a0000000000020020000000000000000000002000000000000000000000000800000000000080002000000000080000000000000000820000000000000800000000000000002000002000000000000000000000000000000002080000080800020000000000000000000020080000000000000082000020000000000800020000000000800000000000000000000000000000002000000000000000000000800000002800000000000000800000000000002080080000000000000000000000000020000000000000000000000000020002000000002000000000000000000800000000000000000000000000020000000000000000000000000000800000020000000000000000800000000000000000800000002000080000000002000020000000000000000000000000000002000000000020080800000000000000000020000000000080000000000000000000000000000002000800000000000000000000002000800000000000000000000000000000000080000000000020000000020000000000080000000002000000000000000000000000000000000000000000800080000000000000020000000000000000000000000000002000000000000020000000000000000000000000000000080000000000000020000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000020000000000000000000000000000002000000000000000800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 2 => 0x20820000000800000000000020008020000000020000200000000200000000000000200000000000000008000000000008000000000000000800000000020000000000000020800800000000200000820000000000000008020000000200000000208000008000800020200000000000000000000008000000200000200000000000000800000000000000000020200000000008000208000800000800000800000000000000020000000000020000000000000000020000000000020000000000800000000000020000008000000008000220020008000000000000000000000008000800000000000200000000000020000000000800000000000000800020020a08208000200000000000008000000000000008000020000000000008000000020000200000000000000028000800000020000000a00000000000000000008000000000000200000000000000000000000020000000008000000200000020000200000200020000000000000020000000000820008208800200028020020200000800008008000000808808000000000000000000200000208020008000000000020000800000020008000000000020000000000000000000200000008000000200000800200000200000000000000020000000200000008000000020800000000000200000008000200020020008000000800000000000800000000020000800200000000800008000800008000000008000000200000000000000020200000000020000008000000000000800000800020000200200000208000200000000000000000800000000a00000000000000000000000808000000000008000000000800220000000800000808000000000000000800000000000020008000000008000020000000800000020008000000200808000000000000020000800200000000000000000000000220200000000000000220008000020000020000800000008000008000000200000000200800000800000200000000000008000000000200000800000000000000820000000000000020000000000000000000000200800008000000000000020000200000000000000008000000000800000000a08200000000000000000000220000008000000000000000200000000000000020000000000000000820000000008008000000220000000008000000008000000000000000000008000000800008008000000800000020000000000800000000000000800000200000208800000000800200800000200000000800000000000000020820008000200000020000000000000000008000000800800000a00000020000008200200220008000000800000008000000000000000000000000008000000000200000000000000000000000000000000200000000200200200000000020008800000000000000000000000000000000808200000800a00000000000000020820000000000000020000000800220000000000000000000200020a00000020020000000000800020000000a08000200000000000000000000000008000008020000000008200000008000000000000800200000000000000000800200000208000000000220000020028000000200200000028800000220000000000000000008000800000000000000a00000020000000000000000000008020000020000000000000000000000000000800000000000000000000000800008008000000200200000800000000008000000000000000800000208000000000000000020000800800000200000000000000800000000020000000000020800000000000808000200000000000008008000000000000000000800000020000000800008008000000000200020000000000000008000000200200000028000000000000000000000000000000000800000000000000000808000020000000008000000000000000020000000000000000200820000000000000200000208000000820000a00020200000000800000000a00000000800000000200000008000000800008020200000200000020000000000000000000000000020008020000808000000000800000000000200000000800000000800000000000000000200000000000000800000000008000208000000008000000020800000000200000800000000000000800000000000000000000000008008020000000808020000000000200000828000200000000000000000000000000200000800800000020000000200000200000000000020008000008200000008200000020008000020000000800000200000000000020000000000800008020000008020200000000028000000000000800000000000000000000028000000000800000000000208000000000000028000000000008800020000000200000800000000000000000000000000220000000200000000000000000000000008000000000008000020800000800000200800000000808000000000828000000000008000000000000800000000000200200008008000000000200000000000000000000208000000000000000200008000000000000a00000000028000800820000000020000000020000200000000020000000000000000008a00000000000008000000220000000220008000000000000000000000220000000200000000000000020000008020800000000000000000000800000000000000008008000000000000000000000820000020000800000000000000000208000000000000000000200000200028008000800800008000000000000000000000000000020800020200000000028000000200000000000000208000000000020200000000000000200800000000000000200000000020000800000200800000000000000000800800000020800008000000008800000000000000000008008020008800000020000000000000000000000000000008000020000000020008000000000800000020000008000000000000000208000000800200000000000020000200000000000000000000200000000008000000020000000000000000200800020000000000200000000000800000808000000000020000020000000008000008000000200800000000800000000000000000028000000000000200000000000000000020000000000000008000800208000008000000000000020020000000000020000800000000000000800000000008000000808000800008000000000000000020000220000000200200000008000000800000800000220000020000000020008000000000200000000800008000000220000000220000000000000200000800000000000000000000000000000000008000000008000008008800000000000000000000800000000020800000000000000200200800000000000000020000000000008800000000000020000000200000800800200000000000000200200008000800000000000000020008000000000000000000000000000008000200800000000020000000000200000000800800020000200000800020800200000000000800200000000000000000020000200800000000020000000000000000000000000000000000020008020808000000000800000000000000000800000020000000000200000200000000000020008000808000000008000000000000000000020000000000000000000000000808000020200000000008000800000000000000000000200000000200000028008000000800200800000000000000000000000000000000200000000000008200000000000020020000000000000020000000008000020000000028000000000200000000208000000000800000800000000000200220000000000008000000000000000000000000000000800000008028000800000200000000000000000020000000000000000200020200000000000020000000000000020800000000000000200000000000000000008000000000008808000000020008800000000000800000000000000000000008208000000200000000020000000000000000800820000000020000808000000000200000000008000200000000020000000020000208000000000000000000000000020000000000008000200000000008000000000000000000000000800200000000000800200000000200008000000020020000000000008000000820000000000000800800000800000008000000000008000000000200000200800200020000000000000000000000800020000000020008000800800008000000000200000000000000000200000000800000200000008000808000000000000000000000000a00000000800000000008200000008000000000000000000800800000000000000800020000000000000000200000000000800200200000000028200000000000800000000008000020000000000020008000020000000000000000008008000000000000020000200000000000008000000000000000000000000000008008800200000000000200000000000000200800028000000000000200000000000000000000020020000000000020020000020800000000000000020020000800000000000000000000000020000000200000200000a00000000000800800000000000800008800000000000208008000000000000000000020000000008008000a00000020000000000800008000000020000000000000000008000020000000000000000008000000000000000000000200008200000000000008000000000000020000000000200000000000000000000200020008220000020000008000000020000000000000000000000000000008000000008000000000000008800000200000000000000000800020000000020200000000020000000000008000200000000000200000000820000000000200200000000000000000000000000000008020020200000000000000020000000008000000000000000000000000200000000000200000000200000008020000000020000808008000020000000000200000000008800000200200008000000000000000008000800000000800020000000800008000000000000000008820000000020000000800000000200000008000000008000000000020020800000800020000000000000000200000000000000000800000000000000200000000000000a00008000000000000800000800200000000000000000000000000020000200800000008000000200000000000000000020000000020800008008008000000000000200000000200000020000000800800000800000000000000000000000000000000000000000020000000008000000800000000020020000000200800000800000000800000000000000000000000000a00000000000000800008000000800200000000000000000000020000000000000200020000000008000020000028000020000200000000000000000008008000000000000020200800000000000008000000000000000000000020000000020000800000008000000000000000000000020800000000008000000008000200000000000000000000020000200200000020000000808000008000000000000000000200008800800000000008200000000200000000000020000000000000000000000800000208000000000000000200800000820000000008200000000000200000000000000000000020020000200000000008000000000000000800000000000000000000020800000000000000000200800000200000000000200000000008000000000000000000000008800000800000000000000200000000000200020000000000000020200000800000000000000000000000000000000200000000000020008000000800000000000800000000020000000000000000000208008000000000000200000000020000000000008020000000000000000808000000000000000020000000000000008000000000000000008000200800000800000000000000000008000000820000200000000020028000000000200008000200000000000000000800000000000000000000000200020800000000000000000000000000800008008008008000000000000000020000000000020000000000800000200000000808000000000000000000a00000000000000020000000000000000000000000000000800000000000000200000008008800000000000200000200000020000000008000000000000800000020000000000a00000008000000208000000800000000000000800000020000208000000000000000000000000000000000000008000000020000000000020000008000000000000000200020208000000000000000000000800000000200000000000000000000800000000800000000000000000000000008020220000000000008000000000000000000800000000020800200000000000220000020000000000000000000020000000200000000000000000000000000800000000000000a00000800000000200000000200000000000008000000200000000000000008020000000000800000000000000000000000000000008200000000a00008000000000000208020000020000000000000000000000000000000000000000800008200000800000000000000000800000020000800020000000000000008000000000000008000000000000000000000000020000000000000800000000000000008000020000000000000008000000000000008a0000000000000000000000080000020000002000000000000000000800002000000002000000020000000000000080000000000080000020000020000000000000000000000000000002000000000800000000000800000000000000000800000000000080000000002000020000020000000000000020000000002000000000020000880000000000000800000000000000080000000000000000000080000000000000800000000000000000000002000800000000000002000000000000000000800000000000020000000000000000000080080000002000000000000000000000000000000000000000000000082000000000000020000800000000000000000000000002000000000000000000000000000020000000000000000080000000000000020000000000000000000000800000000000000000000000800000000000080000000000000000020000000000000020000000000000000000000000000002000000000000000800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 3 => 0x800020020008000000000000200020000028000200020000200000000000000000000000008000000000000000000020000000000000000000000000800200200800008000000020800800000000200000800000000000000020000000000a00020808200000008000800000000000000008000000000000020000200000200000200000000000000000000a00000000200000000008000000000800000020000000000000008000020000008000000000000000000000000000000000000200000008000000000000800000208000000000000220800008000000000800000000020000800000220000000200000000000000000000000800000000200800800000020800208000000000000000008008000000000008000020000000008000000000020000020000000000028000000800000000000000200200000000000000000000000000200000000008200000000000200220000008000000000000000020200000000200000000000008000000000000000020000200000200008020020a20800800008000000000008808000000000000020000000000008000000020000000020000800000000028008800800008000000000000000000200000800000000200000800200000008000000000000028000000200000008000000000000000020000220000008000000020820008000000000000000020000000000000000a00000000000800000000000200000000008000000200000028008000000200000028020000008000000000000000000020020000000000800000000200008000000000000800000000200000000000000000000000828000000000200800000820800220000000000000220000000000000800800000000000000000000000000000000000000000820020000200000200008020000000000020200800200000000020000200200000200000008000000000220008800000000000800800000008000800000008020000000200800000800000000000000000008000000000000200800000000000000028000000000808000000000000800000000000000a00008000008000000200000028000200000000000000000000800000000208000000000020000000000200000008028000000000000200000000000000020008000000000800020000000000008000000220000200008000200008000000000000000000808000a00000000800000000800000020000000000000000000000008000000208000008000020000800000a00008200000800000000000000000220020000000000000000000000008000000208000000000800000800008000000028200000000808000000000000008000200800000000000000000008008000000000200000020800000000020200000008200000000000000000008020020000800000000020000000000000000000000000000000800a00800208000000000020000000200020000000000800020000008000000000000200000200000020000000000020820000000000000000200000000000000000000000008000008020000800808000000008000000000000000008000000000000000800200000208000000000020000008820000000208000000008000200200000000000000800808000800000000020000200000820000000000008008000000020200000020200000000000000000000800000000000000000808000000800000000000000200200000820000000008000000000020000808008000220000200000020000000800800000200000000800000800000200020000000000020800000000000008000000800200000000000000000200000000800008000000000020008000008000000000000020000000800000008000000000200000000000000000000008000000000008000000800020000208000000000000020000000000000000000000000020000000000000800000800000000000000200a00200028000800000200000000000800800000000220000000000000000000020008000000800008000020000200000000200000200800000000000008000000000020008000000200800800000000200000000800020000800000000020000000000000000000000000800000008200200200000000020000020800000000200200800000800000200800000000000008000000000000828020000000808000000000000200000800008000000008000000000000000800200800000800000020000000000000200000000000028008200000200000000200000020000000000008000800000200000000800200000800000000208020000008020000000000000000000020000000000008000000000000000000000020800000020000200008000000000008000000000008800000000000000800808000200000000000000000200200000020200000000000200000000000008000000000008000000000000008000200800200000800000000000a20020020000000800000008000000000000000000200008008000800000000020200000000000000008000000000000000000000000000000000200000000028000000000000000820000200000000200000208020000000000000020008a00000020000000000000020020000220008000008000000000000000200800000000008000000000000000008020800200000000200000000000000020000000000000000000800820020000000000000220000808020000000000000a00000000000000000000200000208020008000000008208000000000008000000020000000800800000200000020008000200000000000000000008800000020000008000000000000000000000000020000200800000020800820000200800000000000000000000000000020820000000000008000200008800000000800000020000a00000020000000000008800000000000000008020020000000000008008000000800800020020000000020000020000008000000000200000000000000000000000000200000008000000800000000000008000200200000000000200800020000000000200000000000800020008008000000020008000020000008000028000000200008000000000008000000020000020000000200000000000008000000800020200000000000008000000008000008020000000000020020000800000000008200000000008000000800200000000000008000820008000000000000200200000000020000200200820000000800808000800008200000000000000020000000000000000000020800020000000220000000020200000000000800000008008000000000000800008000000000000000000008008020000800000000000000200000800000000000000000000000000200000020000000000a00020000000000008000000000000000020000000000000800200000008008800000000008000000020000000000020000800000000000200000000000000008200000800000000820000000000200000000800800000000800000000020000200820000020020000000000000000000020000200800008000000000020000000000000020000200000000020000020000020000000000000008000808000800000220000808000000000200000000000000000000008000200000000000000000000000000000000000000000008000000808000020000000000008008800000000000000800000000000000200000008000000000800000800200000200000000000000000000000200000200000008200020208000020020000200000020000000000000000220000800008000000000200000020208000000000000200800000800000000020000000000028000000000020000000000000000020800000000828000000000200000000020000008020008000000808000200800000208000000020000000000200000800020008000020200020000000200000008000000000008000000000020008000020000800800000000000000800000000000200000200000000000000000000008000000820000020000008008000008000208000000008800000000000020000000020000000000800a00000000000000000020000000200008000000000000000000000000000000000008000000200000008000000000000000000008000008020020000020800008000000020000000000208800000000800008008000000000008000020000220000200800000020000000008000200000200800000800000000008000000800800000000000200000000200000800000000008000000000000028000008000000020000008000000000800000000000000000008200000000800000000000200800800000000000000000200028000000000000000200000000000800220000000000000200000000000800200000000008020000000800020008000020000020800000000000028000000000000000000208200000000008000000000000000000000000000800008a00208000000000000000a00000000200000020000000000800000000000000200800000000020000000000000020000020000000000000000008000000a00000000008020000200000020000000200000000000800808000000000800000000000000200800020000000208000000000000008000000020020000a00000000200000020000000000000208000000000200000000000000008800000000000200000000020800800000000000000800000008000000000000028000000000000020000800000200000000000000000000200000008200008000020000000000020000000200000000820000000000000000000008000200000000000800000200000000008000800800000000000020200000000008000000000800000000000000000200200000800000200800200000000020000000000000000000000808020000000000800000000020000000008000000000000800008000800220000000000200000000000200000020000000000200808008000000000020808200000000000800000200000000020020000000000000000020000000000220000008000008000000000000000008800000200000000000800000800200000000000000008000000008000020800200008000000000000008000000000000800008000800000020000200200000000000000200000000020000000000020820200000000200000000000000000000008000800000008000020200000000000000000000000000020800000000200000000000000000000800200000000000000800000000800200000008008000000000000000000000000000000000200008000000800000008020000000000200800000000000000000000000000028000020000000800000000000808800008000000000220000000000000000000020000800800000200000000000000000020000028000020200000000000000000008828000000800008000000008800000000020000000000000020000000000000000008020000200000008000208000000020000000020000000000000000000000000200008000000000000008020020800000000020000000808000008000000000200000000000008800000200800008200000000000000000008020000000000000000000000000020200020000000000000200000000800000000000000000000800200000000000000800200020000000000000800008000000000800000000000000000000020000020008000200000000000000800000200000000200000020800008000000800000000200000000000000a00000000000000200000200000020020008020000000820000000000000000000000000000000200000000200000000000800000000808800000000000800000000008000008000000000000208028000000000000000000020020000000000008000200000000000000000000000000000800020000000000000008000000000000008000200000800000800000020000000000008000000808000200000000020020000000000200008000000000800000000000200000000200200000000008200020800000000000820000000000000000000008008008020000000000200000000000000020000800008000000a00000000800020000000200000000a00000000000000000000000000000000000800000200000800000008000200200000008200000000800000000000000000000000000008000000000200000000000000000000a20020000000000208000020800000000000000000000020000200000000000800000000000000000000000800000000000000008000800020000000000000000000000200020208000000220000000000000a0800000800000000000000000000002000000080000000000000000000000800002022000000000002800000020000800000000000000000082020080000000022000000800000000000000000000000000000080000000000800000800000000000000020002080000000000000020000000000000000000002000000020000000000000080800000000000080000000000000080000000000800000020000000000000800000000000000802000002000000000000000000000000000000002000000080800020000080000000000000000080000000000000082000020000002000800020000000000800000000000000000000020002000002000000000080000000000800800002800000000000000800000800000002080080000002000000000000080000020000000000000000000020000020002000000002000000000000000000800000000000000000000000000020000000000000002000000000000800000020000000000000000800000000000000000800000082000080000000002000020000000000000000000800000000002000000000020080800000000000000000020000000000080020000000000000000000080000002000800000000000000000000002000800800000000000000000000000000000080000000000020000000020000000020080000000002000000080000000000000000000000000000000000800080000000000000020000002000000000000000000000002000000000000020000000000000000000000080000000080000000000000020000000000000000800000000000000000000000000000800000000000000000000000000000000000000000000020000000000000000000000000000002000000000000000800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 4 => 0x20020008000000000000000800008028800000000000000000000000008000000000000000000000000000000000000008000000000000000000000200020000000000008000800800020000200000020000000000000000000000000800000000200000008000800000000000000000000000000008020000000000200000000000000000000000000000000820200000000008000208000a00000000000000000000000000020000000000000000000000000000000000000000020000000008800000000000000000020000000008800000000008000000000000000000000000800000000000000000000008000020000000200000000000000800000000000000208000200000000000000008000000000000000020000000000008000000020000020000000008000020000800000020000000200000000000000000000000000000200220000000000000000000200000000020008000000000000800000000000200000000000000000000000200000020008000800200028020000220000000008000000000000808000000000000000000200000000020000000000000020000000000000028000800000200000020000000000000200000008000000200020800000000208000000000000020000000000000008000000000000000000000200000008000000200800008000000800000000000000000000000000000000000000800800000800008000000000000000200000008000000000200000008020000000000000000000000000020000000200000000008000000000020000000000800000000000000000000000000000000000000000000208800000000800000000000000200000000000000000800800000000000020000000800000000000000000800020020000000000000808000200000000000000000200000000000000000208000200200000000000000020000800000000000200800000008000000000000000000000200800000800000200000000000008000000000000200000000000000008820000000000000000000000000800000800000000a00008000000000000020000000000000000000000000000000800000000008000000000000000000000000000008000000000000000200000020000000000000000000000000020000000008008000000200000000008000200000000000000000000200000000a00800000000000000000000020000000000000000000000000800000208000000000000000000200000000200000000800000000000000020028000000200000020000000000000020208000000020000000800000000000028200200200008000200800000000000000000000000000000000000008000000000000000000000200000020200000000000000000800000000000000020008800000000800000000000000000000000000200000800800800000000008020800000000000000000000000800020000000020000000000000020200008000000000000020820020000000808000008000000000000000000000000000000020000000008000000008000000000000800200000000000000000000220000008000000000200000000808000000008000000008000000220000008000000000000000800000000000000a00000000000000000000008000000020200020000000000000000000000000800000000000000000000000000000008000000000200000000800000000000000000000800000000000008020000200000000000000800800020000000000000000000000000020000000000028000000000000008000000800000000000008000000000000000000000000020000000008000008000000000000020000000000000008000000200000000000000000000008000000000000000000000000000800200000000000000020000000008000000000000000000000000000000000000800000000008000200800000008000800000200020200000000000000020200000020800000000000000000000000800000000000000200000000000000000000000000000000200008020020008000000000000000000000000200000800000000800000000000000000000000000000000800000000000200200000000000000000000008000000200000800000800000200000000000000000000000000000800020000000008000000000000008000800000200000000000000000000000000200200000800000000020000000000200000000000020008000008000000000000000000000000020000000000000200000000000020000800000000208020000008000000000000000000000000000800000000020000000000008000000800800000020000008000000000000008000000000008000020000000000000008000200000000000000000000220000000000000800000000000000000008000000000008000000800000000000000800000000820000000000008000028000000000000000000000000000000200200000028000000000200000200000000000000200000000000000000000000000000000000000000000028000000800000000020000000000000800000000020000000000000020000a00000020000000000000000000000220008000000000000000000000000000000008000000000000000000000020000200000000000000000000000000000000008000000000800000000000000020000000000000020000000000000200000200000000000000000000200020000000000808208000000000000000000200000000800800000200000000000000000000000000000000208000800000020208000000000000000000000000000000000000000020000800000200000000000000000000800800000020000000000000008000000000000000000800000000008800000020000000000000000000020000800008000000000000000008000000000000000000020008000000000020000000000000800200000008000000000000000000200000200000000000000028000000020000000000000000000800020000000800200000000000800000008008000000020000000200000008000020000000000800000000000000000000000000020000000000000200008008000000000020000000000000008000000000000008020000000000000020000000000000000800000000008000000000000000000000800000020008000000000000200000000020000000000000000008000000800000000000200000020000000020000000000000000000800000008000000200000000220000000000000000000008008000000000000000000000000000000000000008000020000000000000000000000008800000000020000000000000000200000800000000000800000000000000008000000000000000000000000200800800000000008000800200000008000000000800000000020008000000000000000000000000000000000000800000000000000000000200000000008800000000a00000000020000000020000000800000000000000000000020000200800000000000000000000000000000020000000000000020000000008208000000000000000000000000800000200000800800200000200000020000000000000800000000000000000000000000000000000000000000000008000000808000000000000000008000000000000000020000200000000000000000008000000000000200000200000000000000000800000000000200000000000000000000200000020000000000000000000000800000000020000800020000000000200000020208000000000000000000000000000000200000000000008000000000000000000000000000000800000020800000000000000000000020000000020000000000000000000020000008000000020000000000000000800020000200000200000000000200000000000000000000800000000000008000800000800800000000000000000000000008000000200000000000008000000000000000820000000000008008000008020000000000000000200000000000000000000000000000000000000000000000000020020000200000000000000000008000000000000000000000000000a00000000000000000000000000000000000020020000000000008000000020000000000000000800008800000008000000000008000000000000800000020000020000000008000000000000800020800000000000000000800000000000000200000000000000200200000008000000000008000000808000000020000000000000000000000000000000000000200000000000000000000200000000000000000000000000000000000000000000000000000000800200200000000000000000000000000000200000008020000000000020008000000000000000000000008020000200000000000000200000000000008000000000000000000000000000800008800000000000000000000200000000200000000000000000008000000000000000800000000020000000000000020000000000000020000000020000000800000000000000000200000000000000200000000000200800000000000800200000000800000000000000000200000000000000808000000000000000008000000000000020000000000000008000000000200000000000000008000008000000200000000000000800000000000000800020000000000000000008000000000000000008000000200000000000000000000200000000000000020020000000020020000000000000000020000000000000000000008000000000000000000000200000000000000800000000000000020000000000000000008000008000000000000000000000000020000000820200000000020800000000000000000000000020000200000000000000000000000008000000000000000008000000200000000000000000000000000008828000000000000008000000020000000008200000000000800000000000000020000000000000000000000000000000220000000800008000000000000020008000000000000000000000000800200000000000000000000000000020020800000000000000000200008000000000000000008000800000020000000200000000000000800000000020000000000000000000000000200000000000000000000000000800008000000000200000000000000000000000000000800000000000000000000000200000000000000000000000800800000000000000000000000000000000200000000000000000000200008000000000000008800020000000000800000000000000000000000000020000000000000a00000000000000000008000000800200000000000000000000000000000000000200000000000008000000000020000020200000000000000000000808000000800000000000000800000200000000000000000000000000000000000008020800000000000000008000000020000000000000000000008000000000000200000000000000000000020000000000000000000000008000008000000000020000000000000800000000000000200000000000000000008000000000000000000000000000020208200000000000000000000000820000000000000000000000000000000000000000000020000000200000800008000000000000000800000000000000020000000000000000000000000000800000000000000000000020000008000000000000000000000000000000a0000000000000020000020000020002000000000000082000000080000000000000000000000000080000000000000000000000000000800000000000080000000002800000000000000000020800000000800000000000002000000000000000000020000002000000080000000000000080002000000000000000800000000000000000820000000000080000000020000000000000000080000000000000000002000080000020000800020000000000000000000000000000020000000000020000000000000000080000000800000000000800800000800000000000000002000000000000000000000000000020000000080002000000000000000000000000000000000000000000000000000000000020000080000000000000020000080000800000000000000000000000002000000000800000000000000000000000000000080000000000000020000000000000000000000080000002000020000000000000000000000000000000000000000800000000000000080002000000000000000000000000002000800000000000000000000000800000000000000000000000000002000000080000000000000000000000000002020000000000000800000020000000000000000000002080000080000000022000000000000000000000000000000000020000000000000800000000000080000000000000080000000000000020000000000000000000000800000020000000000000000802000000000000000000000000080000000000000000020000000020000000000000000000802000000000000000000000000000000000000002000000080000000000080000000000000000000000002000000002000020000000000800000000000000000000000000000000000000002000000000000080000000000000000800002800000000000000800000000000002800000000000000000000000080000020000000000000000000000000020002000000000000000020000000000000000000000000080000000000000000000000000000000000000000800000000000800000000000800000000000000000000000000000080000000000000020000000000000000000020000000002000000000000000880000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000020000000000000000000000000000002000000000000000000000000000000000000000000000080000000000000020000000000000000000000000000002000000000000000000000000000000000000000000000080000000000000020000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000020000000000000000000000000000002000000000000000800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 5 => 0x800000820000000800000000000820008028000000000000200000000200008000000000008000000000000008000020000008008000000000000800800200020a00000000008020000800020000200000000000000000000000020000000200020008208800000000000000200000000008000000000000020000200000000000200000000800000000000a00000020000000000000000200000a00000800000000000000000000020000008020000000000000000000020000008000000200000008000008000000820000208000000008800220000008000000000800000000020000000800020000000200000008000020000000000800000000200800800020000a08200000000000000000008000000000000000000000000000000008000000020000200000000008028020000000000000200000800200000000020000008000000000200200000000200000000000000020008028000000000200000820200000000000020000000008000020000000000000000208800000020020020a20800800008008000000800008000000000000000000200000208000008020000000000000800000000000008800000228000020000000000000200000808000000000000800000000008000000020000008000000200000000000000020000000020000200000008000200220000000000000800000000000800000000020800a00200000000800800000000208000000008000000200000020000000020000000028020000008200000000000800200820020000200000800200000000000000000000000000000000a00000000000000000000000828000000000008800020000800200000000800000a20000000000000000000000000000000008000000008000020000000800020000008200000200800020200000000020000800200000008020000000200000020000008000000000000008800020000020a00800000200000808000008200000000200800000000000200000000000000000000000200000800000000000008020000000000808020800000000000000000000200200008000008000000028000020000200000000008000000000800000200200200000000020000000000020000008008000000000000000000000800000020000000000000800820000000008000000000000000000008000200008000000000000000000000000800000008808020000800000000000000000800000000000008800020208000208000020000000000a00008000000000800000000000000200820008000000000020000000000000020208000000800800000200000000000008000200220800000200000800008000200000000000000000000000008000000000200000020800200000020000000008200000000a00200200008000020000800000000820000000000000000000000808200000000000800200000000020820000000000020000000000808200000008000000000000200000a00008000020000000020000020000000008000208000000000000000000000008000008020000820000200000008000000000000800008000000200000000000020000208000000000020000020028000000008200000000800200220000000000000800808000000000020020000000000020000000000008000000008000200000028000000000000000000000800800000000000000008000000800008008000000200200000800000000008000000000020000008008200020000000000020000000000000020000000000800000800000000020000000000000800000000000800000000800200000008008000000000000000000008000020020020800008008000000000200000000000800000000000000200200000020020000000008000000000000000000000000020000208000000808000000000000008000000000000008820000000000000000200020000000008000000200208008000820000200000200000000800000000a20000020800000000200020000000000000008020200000000000020000000200800000000000000800000020000800000000000000800000000200200000000020000000000000020000000000000000200000800000000008000208200000008000000020800000000000200000000000000200800000000000008000000000200800000000000808020000000000208000808000200000000000000000000000800000800800800000020020000200020200000000000008000200008000000008200000020008008020008000800000000000000800200000800000800000000000008000200000000020000000000000800000008000000800000000000000820800000020000200008000000000028000000000000800020000800200800000000200000000000000000200000000000200000000000000000000000008000000000200000020000000808000200800200000020000000000a08000020000008800000000000800000000000000200008000000800000000020200000000000000208000000000000000200008000000000000a00000000008000000020000000a00000000020000800000208020000000000000020008800000000008000000000220020000200000000008000000000000000220800000200000000000000020000000020800000000000200000000800000020000000008008000000000000020000000020000220000008020000000000000808000000000800000000000000200008008000800000200000000000000200000200200000800000020000000020028000200200000000000000008800800000020008000000000000000800000020020000200000000020000820000000800000000000000000000800000000020008000000000800000008800000000800008020008000000020000000000008800000020000000008820020000000020000000000000800000000020000000020200000000008000000800000000000000020000200000000200000208000200800000008000008000000200000000000200000020000000800000000000000000020808008000000008008000000000000000028000000200808000000800000000000020000028000000200000000008000000000000000200000000000000000000200000008000000000000020020000a00000020008000000000008000800800000000000000808000020000000000000000000200000200000000200000820008000000808000800008220000020000000000008000000008200000020800020000000200000000220200000000000200000808000000000000000800000000000000008000000000008008000800000000000000200008000000000020800000000000000200200000000000000a00020000000000000800000000000020020000000000800000200000008008000000220008000800020000000000000008800000000000000000008000000000000200800000000820000000000000000000800800020000a00000800000800200000000000820200000000000000000020000200000000000020000000000000000000220000200000000000008020000028000000800000008000008000800000200000000000200000000000020000020000020800000200008000000000000000000000000000000000008008000000008000020200000000008008000000000000000000200000000000200000020008000000800200800200000a00000000000800000000000200000000000008200020008000000000000000000020020000000008000220000000020000000000200000020008000000000800200800000800000200220000000000000000000000020000000000000000020000000008828000000000000000000000000000020000000000008000200820200208000000020000000000000020000020808200020000000000000000000008000000000000808000000020000800800000000800000000000000800000008008200000000000000020000000000008000000800000020020008800000000000008000000008000200000000020000000020000200000800800000000000000000000020000200008000200000000008000000000000000000008000800200000008800800200000000000008000000000020000020800000000200020000000000200000800000000008008000000000008000020000020800200800200000000000000000000000200820020800000000008000800000808000000000000000000208000800200000008800000200008020000800000000020000000000000000a00000000000000000008000000008800000000000200800000800000000000000a00028000000000000000000000000000000220200000000008200000000000800200200008000000000000800020000000000000000800000020008008000000000000020000000200000000008000000008000000000000000000808000a00208000000000200000800000000200800020000000000808200000000000000000000000000000000000020020000020800000020000000028020200200000000008000000200000000000000200000200000a00800000000000800000000000800208800020000000208008000000000008000000020020000208000000a00000000008000000800200000000000000000000000000008800020000000200000000028800000000000000000800200008000000800000020000000000000000008800000200000000000000000000000020000220008020020008000020000000000200000000000000000000008000000008000200000000008000020000000000008000800800020000000000000000000028000000000808000000000000000200200000820000200000000200000020800000000000000000000808020020200000800800000020000000008000000000000000000000800020000200000200000000200000008008000000020200000008000020000020808200000000008000000000000008020000000000000008000820000000000020000000800000000000000000000008820000200020000000800000800000000000000000000000000008020000800200808000000000000008000200800000800000000000000020000200000000000000000a00208000000000000800000820000000000200000000000000000020000200000000008000020000000000000000000020000000000800000008208000000000000200000800200000008000000000800000800000000008008000000000000000000000000000020000200000000000000000000020020000000a00000000000000000800000000000000000020000000a00000000000808800000000000800220000000000000000000000000800000000000000000000008000020000020000000200200000000000000008028008000800008000020008000000000020008000000000000000000000020000008000000a00000008000200000000020000000020800000000008000000000000000008000000000000008020020200200000000000200800000008000000000000000000200000000800200800008000000000000000000008020000000000000000000000020020208020000000000000200800000020000000008200008000800000000000000000800200000020000200000800008000000000000000800000000000000000000000808000000800000000200800000200000000200000020800000000000a00000000200000008000000000000000000000000000200000220020000020000000000200000800000000000000000000000200000000200000000000800008000008800000000000800000000020000008000000000000200028000000000000000000000020000000000000020200000000000000808000000000000800000000000000000000000000000000008008000200000000000000020000000000008000000828000000000000020008000000000200000000200000800000000000800000000200200000000008000000800000000000820000000000000000008008000000000000000000200020000000000020000800000800000800000000800020000000200000000200000000000000000000000000000000000000000200000000000008000200000000008008800000800000000000200000020000000000000000000200000000020000000000220000008000000000000020800000000000000800000000000200000000000800000000000000000000000800008000000020008000800020000008000000000000000000000208000000020000000000000a08000008200000000000000000000020000000800000000000000000000008008000220000000000020000000200000000000800000000020020200800000000020000008000000000000000000020000000200000000000008000008000000800000000200020000000800000000000000000200000000000028000000200000000000000800020000000000800000000000000800000000008000000000000000a00008000000000000208000000020000000000000000000000000000000020000000008008200000800000000000000000800000020000800800000200000020000000200000000008000000000000000000000200020000020000000800800000000008008000008000000000000000000008000000028a0080000002000000000000080000000000002000000000000020000820000000000002000000020000000000800080000000000080000020000020000000000000002000000000000802000020000800000000000000000000000000000800000082000000000000002000000000020000000000000820000000000000000000020080080000000000000800020000000000000020000000000000000080080000002000800000000000000000000002000000800000000002000000000000000000880000000000000000000020000000020080080000000000000080000000000000000000000000000000000800002000000000000000000802000000000000000000000000000000000000020000000000000020000000080000000000000000000000000000000000000000800000800000000000000000000000000000000000080000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6 => 0x800208000000000000200820000000800000020000000000000200000000000000200020000000000800000000000000008000008000000000800000000000008000008000000800000000000000800000000000000008000000000800000000000800000000000020200000000008000000000000000000200000000000000000000800000000020000000800000000000000000000000200000820000800000000000000020000000020020000000000000000000000000000000000000000000008000000000000028000000000000000820000000000000800000000000008800000200000000000000028000000000000200000000000000000008000020a08000000000000000000000008000000000008000000000000008000000800000000020000000000020008000000000000000000800000000000020000000000000000000020000000800000000000220220008000000000000000000800200200000000020000000000000000000200000800000000000000000000000000000000808000000000008000000000000000000200000000200000008000000000000000800000020020000000800008000020000000000000000000000000000000020800208000000000000020000000000000000000000000000000800000000000220000000000200200820000000000000000000000200000000020000200000000000000808000000000000000008000000000000008000000020000000000020000000000000000000000200000000000000200000000000200000020000000000000000000800000800000000000000000000000000000200000020000000220000000000200828800000000000800000000000000000008000820000000000000000000800000000000008000000000200000000020200200000000000000000000008000000000000000000000200008000020000000800000000200200000000000200000000000000000000000000000000000000000000000000200000000000000008000000000000008000008000000800000800000000000008000000000000208000220000000000000008000000000000000000800200000000000000000000200000000000000000000000000000020800000020008000000000000000020000000000000000020000000000000000000000000000000000200808000200000000008000000000000000000000000800800000000000000020000000000800000000800000800008000000000000000000000000000828000000000000000000000008000020000000000020000000200000020000028000000020000000000000800000000000800000000000000000008000000000200200000000000200000000200000000000000000000200000000000000000800000000800000000000000000000000820000000000200000008000008000000008000000000020000000008000000000020000000000000000800008020000000000000020000000000200000200000000000000000000000000000000020000000000000000000000000000000000000000000200000000800000000008000000000020008028800000000200200000020000000000000008000000800008000000000020000000000000800000000000000008000000200000000008200000000000000000000000000000000000000008000000800000028000000200000000020000000000000000000820000800000000000000200000000020000000000020200000000000000000000000000000000000008000000000000200000200000200000000000000000200000000000800000000020000008008008020000000000000000000000000000000000000000000008000000000000000000000000008000000800000800000000000800000000000000000000000000000000800200000000000800200020000000008000000800200000000000000a00000000000000000000020000000020000000000000000008000000000000020220000000000000000000000000000000000008220000000020800000000000800800000000000200200000000000000000000000000000200000000000000000000000000200000000020008000000000008000000000000000008800000000800000000000000000000000208028000000000000000000000000208800820008000000000000000000000000000000200000000000000020000000020200000000000000000200000200000000000000020008008000000000000000000008000800000000000000000200000000000020000000000008000000020000000000000020000800000020000000800000000200000000008000000000028000000000000800000000000000000808000000000020000000000000000000000200000800000200000000000000000000000000000020000000000000000800000000028000000800220020008000008000000000000000200000000000200000020000800000000000000000000000000008000000000000000000008000000000000800000000000000800000000000200000200020000a00000000020000000000000000000000000020800008000000000020000000000000000200000000000000200000000208008000000000020000008000000200000000000000000000000000000000000008000000800800000000000800000000000800000000000000000800000200000800000000200800000008008000000008000000000000000200000220000000020000020000000000000000000200000000000000000000800000000000000000000000200000000028020000000000000020800000000000000000000000000000000000000000800000800000000800000000000000000008008000000000000000000000000000000000020000800000800020000000000000008000000000000020000000000000200020008208000000000000000008000020000000000000000000200000200000000020000008000200000000000000000000000000200800000000000000000020000000000000008000020220000000000000000000220000000000800008000000000000020000000000000000008008000000000000000000000000000000800008000008020000800000020000000a00000000000000000000000000800000000008000000008000800000000000000000200020000200020020000200000000000000808000000000000000000000000000000000000008200000800800020000000220000000000000000000000800000800008000000000000000200000000000008000000000000020008000000000000000200008000000000000000000000000000000000000000000000008000000000000000800000000000020000000200200000000000000000000800000a20000000000000800000000000000000200000000000000008000000008200200000000000000000000000000000000808800020000000000800000000000020000020000000000000000000000000000200000008000000000000000000000000200000a00000000000008000800208000000000000000000800000000000020000800800000000000000020000000008020008000020000000000000000000000020000000000000008000000000008000000000000000000000800000000000020000200200000000000000020000000000800000000000000800000000000800000000000000000000000000200000200000000020000200000000000000800008000200000800008008000000200000000000000000000000000000000800000000020000000000000000800000000000000000000000000000000220008000800000200000000020000000020000000000808000000000000000000020000000000000200020000000800200020000000000000200000000000000000008008000000000000000820000800000000000000000000000008200000000000000000000008000000000000800800000000020000800000008020200000000000800000000000020000000000000208000000208000000000000000000020000000008000200000000000000000000000000000008000000800000000800800000000000200000000008000020000020000000000200800000000000000800000008000000000020000000008000000000200800200020008000000000008000200000000020000000000020000000800000000000000000000800000008000a00000000000000000200008008000000000000000000008000000000200000000800000000008000000000020000000000000000800800000000000008000000000000000000000200000000000000020000000000028000000000000800000200000008000000000000020000000220000020000000020000020000200000000020000008200000000008000000008000000000000000000000000000000000008000200000200000000000000028000000000008000000000000200800000020000000000000000000000000800000020000200008020200000000000000020000000000020000000200000000000000008000000800000200000000000008800000000000000000000000000800000000000000000800008000200000000008000000800200800000020200000000000000000000008200000000000000000800800000000000000000220000200000800000000000000000000020008000000000000000000000008000000000008020000000000000000020000000000000000000820000000000008800000000000000000000008800020000200000000000000800000000000000200000000020000008000000000200000000020200000000000000200820000000000000800000000000000000000000000000000000800800000000000000000000000000000800008000000000000200000000000000000200000808000000020000800008000000000000000000000000000000000220200008000020000000000008000020000000800200000008000000000000000000020000820000000000000000000000000000000008000000008000000000000000000200000020000000200000000200800000000008000000000000000000000000020000000000200000020000000800020008200000000000000000000000000020008000000008000000000000000000000000800000000000020000008000008000000200000000000000000000028000000000000000000200000000000000000000000200000000000000000000000000000000800000008800000000000a00000000800000000000000000000028000000000000000800000000800000000000000000000000200000000000000020000000800000000020000000000000000000008000000000000000000000000008800008000000000008000200000000200000000000000000020000000000020000000000800000000000000008000000000000000000800000000200000000008000000000000000000000000000000a00200000020000200000000020000000000220000000000008000800000000000000000000200000000000000000000000000000000000820000000200000800000000000000000000000000008000008000000200000000000000000000000000000000000000000000000000800000020000000000000020000020000000200808000000000000000000000000000200000000000000000200000000000000000800000200000000000000000000000000000000008000000000800000000000000000000000000000000000800000000000000020020000000800000000000000000000008008000000000000000000000000000008000000200000020000000000000008000000000020000000000000000000000000200000000000000000000000000000000000200000800000000000000200000000020000000000000200000000000000000800000000000000000000000000000000200000000000000000000000000020000000000000000000008000000800000000008000020000000000000000000000000000000000008000000000000000008000000000000000000800000000000000020000008000000000000800000000000000000000000000000000800200000000000000200800000000000000000000000000000000a00000000000000000000020000000000008000000000000000000000000000000020008000000000000000000000000000008000000000000000000000000000000000000000000000000000200000000000000a0000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000800000000000000000000000800000000000000002000000000000000000000000000000080000000000000000000000000000000000000020000000000020000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 7 => 0x220000000000000000000000008000000200000000000000000000008000000000000000000000000800000000000000000000000000000800000000200200000000000000000000020000000000020000000000000020000000000000000800200000000000800000000000000000000000000008000000000000000000000000000000000000000000000000200000000000000208000000000000000000000000008000000000000000020000000000000000020000008000020000000000800000000000000000000000000000800200000000000000000000000000000008000000000800000000000000000020000000000000000000000000800000000000008000200000000000000000000000000000000000000000000008000000000000000000008008000000000000000020200000000000000000000000000000000000000000020008800000000000000000000020008000000000000000000000000000000000000000000000000000000000008000800200000000020200000000000008000000200000000000000000020000000000000020000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000200000000000000000000000200000000000000000000000000000000000000000000000000008000000000000000020000000000000800800000000000000008000800000000000000000000000000000008000000000000000000000000200000000000800000000000000000000000008000000008000000000000000000000000000000000000000000000008000000000000000000820000000000000000000000800000800000000000000000000020000000000008000000000000800000000000000000000000000000000000000000200200000008000000200000000020200000000000000020000000000000000200000000000000000000000020000000000800000000000000000000000008000000000000000000000000000000808000000000000000800000000000000000000200000000000000000000000000008000000000000200000000000000000200000000000000000000000000000000008020000000000800000000000000000000000000000000000000000000000000000000200000200000000000008000000000000000000000000000800000000020000000000000008000000000000000000000000000000000000000000000000200000000000000800800000000000000020000000000200000000000000000000000000000000000000000000008000000000000000200008000200800000000000000000000000000200000000000000000000000000000000000000000000000000000000000800000a00000020000008000000000000000000000000000000000000000000800000000000000000020000000000200000000000000000000000000000000000000000020000000000000000000000000000000000808000008000000000000000000000020000008000000020800000000000000000000000000200000000000000000000020000000000000000200000000020000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000020800000000000000000000000000000000000000000800000000000000000000000000200000000000000000000000000000000000000208200000000000000000000000800000000000000000000800000200000000000000000000000000000800020000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000020000000008008000000000000000000000000000000000000008000000000000000000000000000008000000000000000000000000000000000000000000000020000020000000020000000800000000000000000000000000000000000000000000000000000000000000008000200000000000000000000000800008000000000000000200000000000000220000000000000000800000000000000000000000000200000000800000000000000000000000020000000800000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000800000000000000000000000000000000000000000000000000000020000000000000000008000000000000000000000000000000000000000000020000000000008008000000000000000000000020000000000000000000000000000000000008020000000000000000000008000000000000000000000000000000000000800000000000000000000000000000000000020000020000000000000000000000000000200000000200000000800000000000000000000000000000000000000000000000000000000008000800000000000200000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000800000000020000000000000000000000000000000000000000000000000000008000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000000000000000000000000000000000000000000000000000000000008000000000000800000000000000008000000000200000000000000200000000000000000000000000000000200000000020000200000000000000000000000000000000000800000000000000000000000000000000000000800000000000000000000000000000200000000000000000000000000200000000000000000000000000000000000000000000000000000008000000000000800000000008000000000000200000000000000000000000000000000000000000000000000000000000000000800000020000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000200000000000000800000000000000000000000000000000020000000000000000000000000000000000a0000000000000000000020000000000000000000000000000000000000000000002000000000000000000000080000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000882000000000000000000000000000000000000000000000000000000000000002000000000000020000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000082000000000000000000000000000000000000000800000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000800000800000000000000000000000000000800000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0

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

/- Dyadic verification of all 28,741 endpoint blocks. Numeric batches supply
literal block cutoffs, checked separately before the expensive mask sweep. -/
namespace Astra247824.HardTail.Batch
open Finset

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def block (b cap low : ℕ) : ℤ :=
  Scan.sweep (Cells.eval denomWords) Patterns.word b cap low Scan.roster (2^W-1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def score (b : ℕ) : ℤ := if b < 28741 then block b (stageCap b) (stageFloor b) else 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def tree : ℕ → ℕ → ℤ
  | 0,i => score i
  | k+1,i => tree k i + tree k (i+2^k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem tree_eq (k i : ℕ) : tree k i = ∑ j ∈ range (2^k), score (i+j) := by
  induction k generalizing i with
  | zero => simp [tree]
  | succ k ih =>
    rw [tree,ih,ih,pow_succ,Nat.mul_two,Finset.sum_range_add]
    simp only [Nat.add_assoc]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem equivalent : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H2 ↔
    tree 15 0 = 3098980124 := by
  rw [Scan.h2_iff_sweep (Cells.eval denomWords) Patterns.word]
  · have limited : (∑ b ∈ range 28741, score b) = ∑ b ∈ range (2^15), score b := by
      apply sum_subset (range_mono (by decide))
      intro b _ out
      exact if_neg (by simpa only [mem_range] using out)
    have inside : Scan.total (Cells.eval denomWords) Patterns.word = ∑ b ∈ range 28741, score b := by
      unfold Scan.total
      apply sum_congr rfl
      exact fun b hb => (if_pos (mem_range.mp hb)).symm
    rw [tree_eq,inside,limited]
    simp only [Nat.zero_add]
  · intro b p word prime large low cap _flags
    exact Cells.eval_eq _ (fun {p d} pp big bound pd dy => @denomWords_correct p d pp big bound pd dy)
      b p word prime large (le_trans cap (min_le_left ..))
  · exact fun p _ => Patterns.word_correct p

/- A batch supplies the square-root cap and the lower prime bound for every successive block. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def paramsOk : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i,(cap,low)::cells => (i < 28741 && cap==stageCap i && low==stageFloor i) && paramsOk (i+1) cells

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
def arithmetic : ℕ → List (ℕ × ℕ) → ℤ
  | _, [] => 0
  | i,(cap,low)::cells => block i cap low + arithmetic (i+1) cells

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem sum_batch (xs : List (ℕ×ℕ)) (i : ℕ) (ok : paramsOk i xs=true) :
    arithmetic i xs = ∑ j ∈ range xs.length, score (i+j) := by
  induction xs generalizing i with
  | nil => simp [arithmetic]
  | cons h xs ih =>
    obtain ⟨cap,low⟩ := h
    simp only [paramsOk,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
    rw [arithmetic,ok.1.1.2,ok.1.2,ih _ ok.2,List.length_cons,sum_range_succ']
    simp only [Nat.add_zero,Nat.add_assoc,Nat.add_comm 1]
    rw [show score i = block i (stageCap i) (stageFloor i) from if_pos ok.1.1.1,add_comm]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem checkedBatch (xs : List (ℕ×ℕ)) (i k : ℕ) (len : xs.length=2^k)
    (ok : paramsOk i xs=true) : tree k i = arithmetic i xs := by
  rw [tree_eq,←len]
  exact (sum_batch xs i ok).symm

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem inactive (k i : ℕ) (out : 28741 ≤ i) : tree k i=0 := by
  rw [tree_eq]
  apply sum_eq_zero
  intro _ _
  exact if_neg (by omega)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
theorem join {k i j : ℕ} {a b v : ℤ} (idx : i+2^k=j) (l : tree k i=a)
    (r : tree k j=b) (value : a+b=v) : tree (k+1) i=v := by rw [tree,idx,l,r,value]

end Astra247824.HardTail.Batch


namespace Astra247824.HardTail
open Finset Leaves ArithmeticFunction
private theorem slice_key_col {e : Edge} (he : e ∈ S) : e.2 ∈ stageSet := by
  have h := (mem_filter.mp he).1
  have primes :=
    Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp (mem_filter.mp h).1).1).2
  have ps : e.2 ∈ Nat.primesLE 3006 :=
    (Nat.mem_primesLE (n:=3006) (p:=e.2)).mpr ⟨hard_prime_upper (y:=Y) (e:=e) h,primes⟩
  exact (mem_filter (s:=Nat.primesLE 3006) (p:=fun z : ℕ => 23 < z) (a:=e.2)).mpr
    ⟨ps,(mem_filter.mp he).2⟩

private theorem slice_regroup {A : Type*} [DecidableEq A] (R : Finset A) (B P : Finset ℕ)
    (k : A → ℕ × ℕ) (f : A → ℤ) (row : ∀ e ∈ R, (k e).1 ∈ B)
    (col : ∀ e ∈ R, (k e).2 ∈ P) :
    (∑ e ∈ R, f e) = ∑ b ∈ B, ∑ p ∈ P, ∑ e ∈ R.filter (fun e => k e = (b,p)), f e := by
  have mapped : ∀ e ∈ R, k e ∈ B ×ˢ P := fun e he =>
    Finset.mem_product.mpr ⟨row e he,col e he⟩
  have all := sum_fiberwise_of_maps_to (s:=R) (t:=B ×ˢ P) (g:=k) mapped f
  rw [←all, Finset.sum_product]
end Astra247824.HardTail

namespace Astra247824.HardTail.Scan
open Finset Leaves
private theorem slice_outside (b p : ℕ) (prime : p.Prime) (large : 23 < p)
    (bad : ¬ (stageFloor b < p ∧ p ≤ stageCap b)) : trueCell b p = 0 := by
  have empty : queryDenoms p b=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact bad ⟨floor_of_member prime hd,capped_of_member prime hd⟩
  simp only [trueCell,fibers prime large,empty,image_empty,sum_empty]

private theorem slice_block_exact (b : ℕ) : (roster.map (value b)).sum =
    ∑ p ∈ stageSet, trueCell b p := by
  have idx : roster.toFinset = Nat.primesLE 3006 := by
    ext p; simp only [List.mem_toFinset,roster_mem,Nat.mem_primesLE]
  have nodup : roster.Nodup := roster_sorted.imp (fun h => ne_of_lt h)
  rw [←List.sum_toFinset _ nodup,idx]
  unfold stageSet
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases large : 23 < p
  · rw [if_pos large]
    by_cases inBand : stageFloor b < p ∧ p ≤ stageCap b
    · exact if_pos ⟨large,inBand⟩
    · rw [slice_outside b p (Nat.prime_of_mem_primesLE hp) large inBand]
      exact if_neg (fun h => inBand h.2)
  · rw [if_neg large]
    exact if_neg (fun h => large h.1)
end Astra247824.HardTail.Scan

namespace Astra247824.HardTail.Slice
open Finset Leaves

def edgePrefix (n : ℕ) : ℤ := ∑ e ∈ S.filter (fun e => (key e).1<n), term e
def rowPrefix (n : ℕ) : ℤ := ∑ b ∈ range n, Batch.score b

private theorem one_row (b : ℕ) : Batch.score b = ∑ p ∈ stageSet, Scan.trueCell b p := by
  by_cases live : b<28741
  · rw [Batch.score,if_pos live,Batch.block,
      Scan.sweep_spec (Cells.eval denomWords) Patterns.word _ (fun p _ => Patterns.word_correct p)
        b Scan.roster [] _ rfl (by intro i hi; simp [Nat.testBit_two_pow_sub_one,hi]),Scan.slice_block_exact]
    intro b p word prime large low cap flags
    exact (Cells.eval_eq _ (fun {p d} pp big bound pd dy => @denomWords_correct p d pp big bound pd dy)
      b p word prime large (le_trans cap (min_le_left ..))).trans (cell_sound prime large flags).symm
  · rw [Batch.score,if_neg live]
    symm
    apply sum_eq_zero
    intro p _
    unfold Scan.trueCell
    apply sum_eq_zero
    intro e he
    obtain ⟨hs,atb⟩ := mem_filter.mp he
    have small := endpoints_bound hs
    have same : X/(e.1*e.2)/W=b := congrArg Prod.fst atb
    exact (live (same ▸ small)).elim

theorem prefix_eq (n : ℕ) : edgePrefix n = rowPrefix n := by
  let A := S.filter (fun e => (key e).1<n)
  have grouped := slice_regroup A (range n) stageSet key term
    (fun _ h => mem_range.mpr (mem_filter.mp h).2) (fun _ h => slice_key_col (mem_filter.mp h).1)
  change (∑ e ∈ A, term e) = ∑ b ∈ range n, Batch.score b
  rw [grouped]
  apply sum_congr rfl
  intro b hb
  rw [one_row]
  apply sum_congr rfl
  intro p _
  unfold Scan.trueCell
  have fibers : A.filter (fun e => key e=(b,p)) = S.filter (fun e => key e=(b,p)) := by
    ext e
    simp only [A,mem_filter]
    constructor
    · exact fun ⟨⟨h,_⟩,k⟩ => ⟨h,k⟩
    · rintro ⟨h,k⟩
      exact ⟨⟨h,by rw [k]; exact mem_range.mp hb⟩,k⟩
  rw [fibers]

theorem full_eq : (∑ e ∈ S, term e) = rowPrefix 32768 := by
  rw [←prefix_eq,edgePrefix]
  have same : S.filter (fun e => (key e).1<32768) = S := by
    ext e
    constructor
    · exact fun he => (mem_filter.mp he).1
    · intro he
      exact mem_filter.mpr ⟨he,(endpoints_bound he).trans (by decide)⟩
  rw [same]

theorem tree_interval (k i : ℕ) : Batch.tree k i = rowPrefix (i+2^k)-rowPrefix i := by
  induction k generalizing i with
  | zero => simp [Batch.tree,rowPrefix,sum_range_succ]
  | succ k ih =>
    rw [Batch.tree,ih,ih]
    have step : i+2^k+2^k=i+2^(k+1) := by rw [pow_succ]; omega
    rw [step]
    omega

theorem join_intervals {a b c : ℕ} {x y : ℤ} (l : rowPrefix b-rowPrefix a=x)
    (r : rowPrefix c-rowPrefix b=y) : rowPrefix c-rowPrefix a=x+y := by omega

end Astra247824.HardTail.Slice


namespace Astra247824.HardTail.Slice
open Finset Leaves ArithmeticFunction
private def sourcePrefix (bound : ℕ) : ℤ :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  ∑ e ∈ S.filter (fun e => t e/65536 < bound), -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ)
private def sourceTotal : ℤ :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  ∑ e ∈ S, -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ)
private theorem prefix_original (n : ℕ) : sourcePrefix n = edgePrefix n := by
  let R := ((special Y).filter (fun e => e.2^2≤X/(e.1*e.2))).filter (fun e => 23<e.2)
  have idx : R=S := by ext e; simp only [R,S,hardEdges,mem_filter,not_lt]
  change (∑ e ∈ R.filter (fun e => (key e).1<n), term e) = _
  simp only [idx,edgePrefix]
private theorem total_original : sourceTotal = ∑ e ∈ S, term e := by
  let R := ((special Y).filter (fun e => e.2^2≤X/(e.1*e.2))).filter (fun e => 23<e.2)
  have idx : R=S := by ext e; simp only [R,S,hardEdges,mem_filter,not_lt]
  change (∑ e ∈ R, term e) = _
  rw [idx]
end Astra247824.HardTail.Slice


namespace Astra247824.HardTail.Batch
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_128 : PLift (tree 0 128 = (8448264 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_129 : PLift (tree 0 129 = (8352690 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_128 : PLift (tree 1 128 = (16800954 : ℤ)) := ⟨join (by decide) b_0_128.down b_0_129.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_130 : PLift (tree 0 130 = (8295847 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_131 : PLift (tree 0 131 = (8129303 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_130 : PLift (tree 1 130 = (16425150 : ℤ)) := ⟨join (by decide) b_0_130.down b_0_131.down (by decide)⟩
private def b_2_128 : PLift (tree 2 128 = (33226104 : ℤ)) := ⟨join (by decide) b_1_128.down b_1_130.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_132 : PLift (tree 0 132 = (7870378 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_133 : PLift (tree 0 133 = (7800994 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_132 : PLift (tree 1 132 = (15671372 : ℤ)) := ⟨join (by decide) b_0_132.down b_0_133.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_134 : PLift (tree 0 134 = (7774061 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_135 : PLift (tree 0 135 = (7481294 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_134 : PLift (tree 1 134 = (15255355 : ℤ)) := ⟨join (by decide) b_0_134.down b_0_135.down (by decide)⟩
private def b_2_132 : PLift (tree 2 132 = (30926727 : ℤ)) := ⟨join (by decide) b_1_132.down b_1_134.down (by decide)⟩
private def b_3_128 : PLift (tree 3 128 = (64152831 : ℤ)) := ⟨join (by decide) b_2_128.down b_2_132.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_136 : PLift (tree 0 136 = (7828762 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_137 : PLift (tree 0 137 = (7566721 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_136 : PLift (tree 1 136 = (15395483 : ℤ)) := ⟨join (by decide) b_0_136.down b_0_137.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_138 : PLift (tree 0 138 = (7494538 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_139 : PLift (tree 0 139 = (7258934 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_138 : PLift (tree 1 138 = (14753472 : ℤ)) := ⟨join (by decide) b_0_138.down b_0_139.down (by decide)⟩
private def b_2_136 : PLift (tree 2 136 = (30148955 : ℤ)) := ⟨join (by decide) b_1_136.down b_1_138.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_140 : PLift (tree 0 140 = (7374976 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_141 : PLift (tree 0 141 = (7270985 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_140 : PLift (tree 1 140 = (14645961 : ℤ)) := ⟨join (by decide) b_0_140.down b_0_141.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_142 : PLift (tree 0 142 = (6962258 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_143 : PLift (tree 0 143 = (7017639 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_142 : PLift (tree 1 142 = (13979897 : ℤ)) := ⟨join (by decide) b_0_142.down b_0_143.down (by decide)⟩
private def b_2_140 : PLift (tree 2 140 = (28625858 : ℤ)) := ⟨join (by decide) b_1_140.down b_1_142.down (by decide)⟩
private def b_3_136 : PLift (tree 3 136 = (58774813 : ℤ)) := ⟨join (by decide) b_2_136.down b_2_140.down (by decide)⟩
def b_4_128 : PLift (tree 4 128 = (122927644 : ℤ)) := ⟨join (by decide) b_3_128.down b_3_136.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_144 : PLift (tree 0 144 = (6860956 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_145 : PLift (tree 0 145 = (6810924 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_144 : PLift (tree 1 144 = (13671880 : ℤ)) := ⟨join (by decide) b_0_144.down b_0_145.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_146 : PLift (tree 0 146 = (6817751 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_147 : PLift (tree 0 147 = (6903234 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_146 : PLift (tree 1 146 = (13720985 : ℤ)) := ⟨join (by decide) b_0_146.down b_0_147.down (by decide)⟩
private def b_2_144 : PLift (tree 2 144 = (27392865 : ℤ)) := ⟨join (by decide) b_1_144.down b_1_146.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_148 : PLift (tree 0 148 = (6769014 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_149 : PLift (tree 0 149 = (6662921 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_148 : PLift (tree 1 148 = (13431935 : ℤ)) := ⟨join (by decide) b_0_148.down b_0_149.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_150 : PLift (tree 0 150 = (6554451 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_151 : PLift (tree 0 151 = (6479757 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_150 : PLift (tree 1 150 = (13034208 : ℤ)) := ⟨join (by decide) b_0_150.down b_0_151.down (by decide)⟩
private def b_2_148 : PLift (tree 2 148 = (26466143 : ℤ)) := ⟨join (by decide) b_1_148.down b_1_150.down (by decide)⟩
private def b_3_144 : PLift (tree 3 144 = (53859008 : ℤ)) := ⟨join (by decide) b_2_144.down b_2_148.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_152 : PLift (tree 0 152 = (6459633 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_153 : PLift (tree 0 153 = (6446966 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_152 : PLift (tree 1 152 = (12906599 : ℤ)) := ⟨join (by decide) b_0_152.down b_0_153.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_154 : PLift (tree 0 154 = (6274638 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_155 : PLift (tree 0 155 = (6208162 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_154 : PLift (tree 1 154 = (12482800 : ℤ)) := ⟨join (by decide) b_0_154.down b_0_155.down (by decide)⟩
private def b_2_152 : PLift (tree 2 152 = (25389399 : ℤ)) := ⟨join (by decide) b_1_152.down b_1_154.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_156 : PLift (tree 0 156 = (6153623 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_157 : PLift (tree 0 157 = (6118769 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_156 : PLift (tree 1 156 = (12272392 : ℤ)) := ⟨join (by decide) b_0_156.down b_0_157.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_158 : PLift (tree 0 158 = (6043491 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_159 : PLift (tree 0 159 = (5933508 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_158 : PLift (tree 1 158 = (11976999 : ℤ)) := ⟨join (by decide) b_0_158.down b_0_159.down (by decide)⟩
private def b_2_156 : PLift (tree 2 156 = (24249391 : ℤ)) := ⟨join (by decide) b_1_156.down b_1_158.down (by decide)⟩
private def b_3_152 : PLift (tree 3 152 = (49638790 : ℤ)) := ⟨join (by decide) b_2_152.down b_2_156.down (by decide)⟩
def b_4_144 : PLift (tree 4 144 = (103497798 : ℤ)) := ⟨join (by decide) b_3_144.down b_3_152.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_160 : PLift (tree 0 160 = (5965892 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_161 : PLift (tree 0 161 = (5998513 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_160 : PLift (tree 1 160 = (11964405 : ℤ)) := ⟨join (by decide) b_0_160.down b_0_161.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_162 : PLift (tree 0 162 = (5873741 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_163 : PLift (tree 0 163 = (5819381 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_162 : PLift (tree 1 162 = (11693122 : ℤ)) := ⟨join (by decide) b_0_162.down b_0_163.down (by decide)⟩
private def b_2_160 : PLift (tree 2 160 = (23657527 : ℤ)) := ⟨join (by decide) b_1_160.down b_1_162.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_164 : PLift (tree 0 164 = (5767463 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_165 : PLift (tree 0 165 = (5698101 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_164 : PLift (tree 1 164 = (11465564 : ℤ)) := ⟨join (by decide) b_0_164.down b_0_165.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_166 : PLift (tree 0 166 = (5647763 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_167 : PLift (tree 0 167 = (5590625 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_166 : PLift (tree 1 166 = (11238388 : ℤ)) := ⟨join (by decide) b_0_166.down b_0_167.down (by decide)⟩
private def b_2_164 : PLift (tree 2 164 = (22703952 : ℤ)) := ⟨join (by decide) b_1_164.down b_1_166.down (by decide)⟩
private def b_3_160 : PLift (tree 3 160 = (46361479 : ℤ)) := ⟨join (by decide) b_2_160.down b_2_164.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_168 : PLift (tree 0 168 = (5529605 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_169 : PLift (tree 0 169 = (5557978 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_168 : PLift (tree 1 168 = (11087583 : ℤ)) := ⟨join (by decide) b_0_168.down b_0_169.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_170 : PLift (tree 0 170 = (5468226 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_171 : PLift (tree 0 171 = (5325322 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_170 : PLift (tree 1 170 = (10793548 : ℤ)) := ⟨join (by decide) b_0_170.down b_0_171.down (by decide)⟩
private def b_2_168 : PLift (tree 2 168 = (21881131 : ℤ)) := ⟨join (by decide) b_1_168.down b_1_170.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_172 : PLift (tree 0 172 = (5249395 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_173 : PLift (tree 0 173 = (5276146 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_172 : PLift (tree 1 172 = (10525541 : ℤ)) := ⟨join (by decide) b_0_172.down b_0_173.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_174 : PLift (tree 0 174 = (5379403 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_175 : PLift (tree 0 175 = (5110838 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_174 : PLift (tree 1 174 = (10490241 : ℤ)) := ⟨join (by decide) b_0_174.down b_0_175.down (by decide)⟩
private def b_2_172 : PLift (tree 2 172 = (21015782 : ℤ)) := ⟨join (by decide) b_1_172.down b_1_174.down (by decide)⟩
private def b_3_168 : PLift (tree 3 168 = (42896913 : ℤ)) := ⟨join (by decide) b_2_168.down b_2_172.down (by decide)⟩
private def b_4_160 : PLift (tree 4 160 = (89258392 : ℤ)) := ⟨join (by decide) b_3_160.down b_3_168.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_176 : PLift (tree 0 176 = (5299317 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_177 : PLift (tree 0 177 = (5141540 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_176 : PLift (tree 1 176 = (10440857 : ℤ)) := ⟨join (by decide) b_0_176.down b_0_177.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_178 : PLift (tree 0 178 = (5219909 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_179 : PLift (tree 0 179 = (4930947 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_178 : PLift (tree 1 178 = (10150856 : ℤ)) := ⟨join (by decide) b_0_178.down b_0_179.down (by decide)⟩
private def b_2_176 : PLift (tree 2 176 = (20591713 : ℤ)) := ⟨join (by decide) b_1_176.down b_1_178.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_180 : PLift (tree 0 180 = (5034859 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_181 : PLift (tree 0 181 = (4749048 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_180 : PLift (tree 1 180 = (9783907 : ℤ)) := ⟨join (by decide) b_0_180.down b_0_181.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_182 : PLift (tree 0 182 = (4844972 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_183 : PLift (tree 0 183 = (4918016 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_182 : PLift (tree 1 182 = (9762988 : ℤ)) := ⟨join (by decide) b_0_182.down b_0_183.down (by decide)⟩
private def b_2_180 : PLift (tree 2 180 = (19546895 : ℤ)) := ⟨join (by decide) b_1_180.down b_1_182.down (by decide)⟩
private def b_3_176 : PLift (tree 3 176 = (40138608 : ℤ)) := ⟨join (by decide) b_2_176.down b_2_180.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_184 : PLift (tree 0 184 = (4806467 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_185 : PLift (tree 0 185 = (4701903 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_184 : PLift (tree 1 184 = (9508370 : ℤ)) := ⟨join (by decide) b_0_184.down b_0_185.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_186 : PLift (tree 0 186 = (4759321 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_187 : PLift (tree 0 187 = (4684701 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_186 : PLift (tree 1 186 = (9444022 : ℤ)) := ⟨join (by decide) b_0_186.down b_0_187.down (by decide)⟩
private def b_2_184 : PLift (tree 2 184 = (18952392 : ℤ)) := ⟨join (by decide) b_1_184.down b_1_186.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_188 : PLift (tree 0 188 = (4574056 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_189 : PLift (tree 0 189 = (4531097 : ℤ)) := ⟨by decide +kernel⟩
private def b_1_188 : PLift (tree 1 188 = (9105153 : ℤ)) := ⟨join (by decide) b_0_188.down b_0_189.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_190 : PLift (tree 1 190 = (9016565 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_188 : PLift (tree 2 188 = (18121718 : ℤ)) := ⟨join (by decide) b_1_188.down b_1_190.down (by decide)⟩
private def b_3_184 : PLift (tree 3 184 = (37074110 : ℤ)) := ⟨join (by decide) b_2_184.down b_2_188.down (by decide)⟩
private def b_4_176 : PLift (tree 4 176 = (77212718 : ℤ)) := ⟨join (by decide) b_3_176.down b_3_184.down (by decide)⟩
def b_5_160 : PLift (tree 5 160 = (166471110 : ℤ)) := ⟨join (by decide) b_4_160.down b_4_176.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_192 : PLift (tree 1 192 = (9174797 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_194 : PLift (tree 1 194 = (9079167 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_192 : PLift (tree 2 192 = (18253964 : ℤ)) := ⟨join (by decide) b_1_192.down b_1_194.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_196 : PLift (tree 1 196 = (8760217 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_198 : PLift (tree 1 198 = (8504042 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_196 : PLift (tree 2 196 = (17264259 : ℤ)) := ⟨join (by decide) b_1_196.down b_1_198.down (by decide)⟩
private def b_3_192 : PLift (tree 3 192 = (35518223 : ℤ)) := ⟨join (by decide) b_2_192.down b_2_196.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_200 : PLift (tree 1 200 = (8562666 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_202 : PLift (tree 1 202 = (8223755 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_200 : PLift (tree 2 200 = (16786421 : ℤ)) := ⟨join (by decide) b_1_200.down b_1_202.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_204 : PLift (tree 1 204 = (8058655 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_206 : PLift (tree 1 206 = (7923958 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_204 : PLift (tree 2 204 = (15982613 : ℤ)) := ⟨join (by decide) b_1_204.down b_1_206.down (by decide)⟩
private def b_3_200 : PLift (tree 3 200 = (32769034 : ℤ)) := ⟨join (by decide) b_2_200.down b_2_204.down (by decide)⟩
private def b_4_192 : PLift (tree 4 192 = (68287257 : ℤ)) := ⟨join (by decide) b_3_192.down b_3_200.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_208 : PLift (tree 1 208 = (7931751 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_210 : PLift (tree 1 210 = (7710458 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_208 : PLift (tree 2 208 = (15642209 : ℤ)) := ⟨join (by decide) b_1_208.down b_1_210.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_212 : PLift (tree 1 212 = (7734416 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_214 : PLift (tree 1 214 = (7720599 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_212 : PLift (tree 2 212 = (15455015 : ℤ)) := ⟨join (by decide) b_1_212.down b_1_214.down (by decide)⟩
private def b_3_208 : PLift (tree 3 208 = (31097224 : ℤ)) := ⟨join (by decide) b_2_208.down b_2_212.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_216 : PLift (tree 1 216 = (7401133 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_218 : PLift (tree 1 218 = (7345676 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_216 : PLift (tree 2 216 = (14746809 : ℤ)) := ⟨join (by decide) b_1_216.down b_1_218.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_220 : PLift (tree 1 220 = (7278532 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_222 : PLift (tree 1 222 = (7120094 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_220 : PLift (tree 2 220 = (14398626 : ℤ)) := ⟨join (by decide) b_1_220.down b_1_222.down (by decide)⟩
private def b_3_216 : PLift (tree 3 216 = (29145435 : ℤ)) := ⟨join (by decide) b_2_216.down b_2_220.down (by decide)⟩
private def b_4_208 : PLift (tree 4 208 = (60242659 : ℤ)) := ⟨join (by decide) b_3_208.down b_3_216.down (by decide)⟩
def b_5_192 : PLift (tree 5 192 = (128529916 : ℤ)) := ⟨join (by decide) b_4_192.down b_4_208.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_224 : PLift (tree 1 224 = (7154474 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_226 : PLift (tree 1 226 = (7098624 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_224 : PLift (tree 2 224 = (14253098 : ℤ)) := ⟨join (by decide) b_1_224.down b_1_226.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_228 : PLift (tree 1 228 = (6854865 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_230 : PLift (tree 1 230 = (6795612 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_228 : PLift (tree 2 228 = (13650477 : ℤ)) := ⟨join (by decide) b_1_228.down b_1_230.down (by decide)⟩
private def b_3_224 : PLift (tree 3 224 = (27903575 : ℤ)) := ⟨join (by decide) b_2_224.down b_2_228.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_232 : PLift (tree 1 232 = (6624627 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_234 : PLift (tree 1 234 = (6588590 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_232 : PLift (tree 2 232 = (13213217 : ℤ)) := ⟨join (by decide) b_1_232.down b_1_234.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_236 : PLift (tree 1 236 = (6296633 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_238 : PLift (tree 1 238 = (6315813 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_236 : PLift (tree 2 236 = (12612446 : ℤ)) := ⟨join (by decide) b_1_236.down b_1_238.down (by decide)⟩
private def b_3_232 : PLift (tree 3 232 = (25825663 : ℤ)) := ⟨join (by decide) b_2_232.down b_2_236.down (by decide)⟩
private def b_4_224 : PLift (tree 4 224 = (53729238 : ℤ)) := ⟨join (by decide) b_3_224.down b_3_232.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_240 : PLift (tree 1 240 = (6307492 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_242 : PLift (tree 1 242 = (6153099 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_240 : PLift (tree 2 240 = (12460591 : ℤ)) := ⟨join (by decide) b_1_240.down b_1_242.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_244 : PLift (tree 1 244 = (6198472 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_246 : PLift (tree 1 246 = (5960553 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_244 : PLift (tree 2 244 = (12159025 : ℤ)) := ⟨join (by decide) b_1_244.down b_1_246.down (by decide)⟩
private def b_3_240 : PLift (tree 3 240 = (24619616 : ℤ)) := ⟨join (by decide) b_2_240.down b_2_244.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_248 : PLift (tree 1 248 = (5882937 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_250 : PLift (tree 1 250 = (5624826 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_248 : PLift (tree 2 248 = (11507763 : ℤ)) := ⟨join (by decide) b_1_248.down b_1_250.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_252 : PLift (tree 1 252 = (5749739 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_254 : PLift (tree 1 254 = (5608863 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_252 : PLift (tree 2 252 = (11358602 : ℤ)) := ⟨join (by decide) b_1_252.down b_1_254.down (by decide)⟩
private def b_3_248 : PLift (tree 3 248 = (22866365 : ℤ)) := ⟨join (by decide) b_2_248.down b_2_252.down (by decide)⟩
private def b_4_240 : PLift (tree 4 240 = (47485981 : ℤ)) := ⟨join (by decide) b_3_240.down b_3_248.down (by decide)⟩
def b_5_224 : PLift (tree 5 224 = (101215219 : ℤ)) := ⟨join (by decide) b_4_224.down b_4_240.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_256 : PLift (tree 1 256 = (5561730 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_258 : PLift (tree 1 258 = (5547114 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_256 : PLift (tree 2 256 = (11108844 : ℤ)) := ⟨join (by decide) b_1_256.down b_1_258.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_260 : PLift (tree 1 260 = (5484135 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_262 : PLift (tree 1 262 = (5316482 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_260 : PLift (tree 2 260 = (10800617 : ℤ)) := ⟨join (by decide) b_1_260.down b_1_262.down (by decide)⟩
private def b_3_256 : PLift (tree 3 256 = (21909461 : ℤ)) := ⟨join (by decide) b_2_256.down b_2_260.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_264 : PLift (tree 1 264 = (5360934 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_266 : PLift (tree 1 266 = (5318896 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_264 : PLift (tree 2 264 = (10679830 : ℤ)) := ⟨join (by decide) b_1_264.down b_1_266.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_268 : PLift (tree 1 268 = (5306776 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_270 : PLift (tree 1 270 = (5210330 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_268 : PLift (tree 2 268 = (10517106 : ℤ)) := ⟨join (by decide) b_1_268.down b_1_270.down (by decide)⟩
private def b_3_264 : PLift (tree 3 264 = (21196936 : ℤ)) := ⟨join (by decide) b_2_264.down b_2_268.down (by decide)⟩
private def b_4_256 : PLift (tree 4 256 = (43106397 : ℤ)) := ⟨join (by decide) b_3_256.down b_3_264.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_272 : PLift (tree 1 272 = (5074151 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_274 : PLift (tree 1 274 = (5140080 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_272 : PLift (tree 2 272 = (10214231 : ℤ)) := ⟨join (by decide) b_1_272.down b_1_274.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_276 : PLift (tree 1 276 = (5003845 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_278 : PLift (tree 1 278 = (4842274 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_276 : PLift (tree 2 276 = (9846119 : ℤ)) := ⟨join (by decide) b_1_276.down b_1_278.down (by decide)⟩
private def b_3_272 : PLift (tree 3 272 = (20060350 : ℤ)) := ⟨join (by decide) b_2_272.down b_2_276.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_280 : PLift (tree 1 280 = (4806739 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_282 : PLift (tree 1 282 = (4903590 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_280 : PLift (tree 2 280 = (9710329 : ℤ)) := ⟨join (by decide) b_1_280.down b_1_282.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_284 : PLift (tree 1 284 = (4891567 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_286 : PLift (tree 1 286 = (4848053 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_284 : PLift (tree 2 284 = (9739620 : ℤ)) := ⟨join (by decide) b_1_284.down b_1_286.down (by decide)⟩
private def b_3_280 : PLift (tree 3 280 = (19449949 : ℤ)) := ⟨join (by decide) b_2_280.down b_2_284.down (by decide)⟩
private def b_4_272 : PLift (tree 4 272 = (39510299 : ℤ)) := ⟨join (by decide) b_3_272.down b_3_280.down (by decide)⟩
private def b_5_256 : PLift (tree 5 256 = (82616696 : ℤ)) := ⟨join (by decide) b_4_256.down b_4_272.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_288 : PLift (tree 1 288 = (4678701 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_1_290 : PLift (tree 1 290 = (4823823 : ℤ)) := ⟨by decide +kernel⟩
private def b_2_288 : PLift (tree 2 288 = (9502524 : ℤ)) := ⟨join (by decide) b_1_288.down b_1_290.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_292 : PLift (tree 2 292 = (9349172 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_288 : PLift (tree 3 288 = (18851696 : ℤ)) := ⟨join (by decide) b_2_288.down b_2_292.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_296 : PLift (tree 2 296 = (8816666 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_300 : PLift (tree 2 300 = (9054251 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_296 : PLift (tree 3 296 = (17870917 : ℤ)) := ⟨join (by decide) b_2_296.down b_2_300.down (by decide)⟩
private def b_4_288 : PLift (tree 4 288 = (36722613 : ℤ)) := ⟨join (by decide) b_3_288.down b_3_296.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_304 : PLift (tree 2 304 = (8607570 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_308 : PLift (tree 2 308 = (8333812 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_304 : PLift (tree 3 304 = (16941382 : ℤ)) := ⟨join (by decide) b_2_304.down b_2_308.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_312 : PLift (tree 2 312 = (8384479 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_316 : PLift (tree 2 316 = (8137405 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_312 : PLift (tree 3 312 = (16521884 : ℤ)) := ⟨join (by decide) b_2_312.down b_2_316.down (by decide)⟩
private def b_4_304 : PLift (tree 4 304 = (33463266 : ℤ)) := ⟨join (by decide) b_3_304.down b_3_312.down (by decide)⟩
private def b_5_288 : PLift (tree 5 288 = (70185879 : ℤ)) := ⟨join (by decide) b_4_288.down b_4_304.down (by decide)⟩
def b_6_256 : PLift (tree 6 256 = (152802575 : ℤ)) := ⟨join (by decide) b_5_256.down b_5_288.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_320 : PLift (tree 2 320 = (7726422 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_324 : PLift (tree 2 324 = (7545544 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_320 : PLift (tree 3 320 = (15271966 : ℤ)) := ⟨join (by decide) b_2_320.down b_2_324.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_328 : PLift (tree 2 328 = (7842077 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_332 : PLift (tree 2 332 = (7156458 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_328 : PLift (tree 3 328 = (14998535 : ℤ)) := ⟨join (by decide) b_2_328.down b_2_332.down (by decide)⟩
private def b_4_320 : PLift (tree 4 320 = (30270501 : ℤ)) := ⟨join (by decide) b_3_320.down b_3_328.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_336 : PLift (tree 2 336 = (7182146 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_340 : PLift (tree 2 340 = (7225090 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_336 : PLift (tree 3 336 = (14407236 : ℤ)) := ⟨join (by decide) b_2_336.down b_2_340.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_344 : PLift (tree 2 344 = (6859696 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_348 : PLift (tree 2 348 = (6909667 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_344 : PLift (tree 3 344 = (13769363 : ℤ)) := ⟨join (by decide) b_2_344.down b_2_348.down (by decide)⟩
private def b_4_336 : PLift (tree 4 336 = (28176599 : ℤ)) := ⟨join (by decide) b_3_336.down b_3_344.down (by decide)⟩
private def b_5_320 : PLift (tree 5 320 = (58447100 : ℤ)) := ⟨join (by decide) b_4_320.down b_4_336.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_352 : PLift (tree 2 352 = (6949358 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_356 : PLift (tree 2 356 = (6811611 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_352 : PLift (tree 3 352 = (13760969 : ℤ)) := ⟨join (by decide) b_2_352.down b_2_356.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_360 : PLift (tree 2 360 = (6435968 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_364 : PLift (tree 2 364 = (6351151 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_360 : PLift (tree 3 360 = (12787119 : ℤ)) := ⟨join (by decide) b_2_360.down b_2_364.down (by decide)⟩
private def b_4_352 : PLift (tree 4 352 = (26548088 : ℤ)) := ⟨join (by decide) b_3_352.down b_3_360.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_368 : PLift (tree 2 368 = (6259605 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_372 : PLift (tree 2 372 = (6342225 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_368 : PLift (tree 3 368 = (12601830 : ℤ)) := ⟨join (by decide) b_2_368.down b_2_372.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_376 : PLift (tree 2 376 = (6130985 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_380 : PLift (tree 2 380 = (5853861 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_376 : PLift (tree 3 376 = (11984846 : ℤ)) := ⟨join (by decide) b_2_376.down b_2_380.down (by decide)⟩
private def b_4_368 : PLift (tree 4 368 = (24586676 : ℤ)) := ⟨join (by decide) b_3_368.down b_3_376.down (by decide)⟩
private def b_5_352 : PLift (tree 5 352 = (51134764 : ℤ)) := ⟨join (by decide) b_4_352.down b_4_368.down (by decide)⟩
def b_6_320 : PLift (tree 6 320 = (109581864 : ℤ)) := ⟨join (by decide) b_5_320.down b_5_352.down (by decide)⟩
private def b_5_128 : PLift (tree 5 128 = (226425442 : ℤ)) := ⟨join (by decide) b_4_128.down b_4_144.down (by decide)⟩
private def b_6_128 : PLift (tree 6 128 = (392896552 : ℤ)) := ⟨join (by decide) b_5_128.down b_5_160.down (by decide)⟩
private def b_6_192 : PLift (tree 6 192 = (229745135 : ℤ)) := ⟨join (by decide) b_5_192.down b_5_224.down (by decide)⟩
private def b_7_128 : PLift (tree 7 128 = (622641687 : ℤ)) := ⟨join (by decide) b_6_128.down b_6_192.down (by decide)⟩
private def b_7_256 : PLift (tree 7 256 = (262384439 : ℤ)) := ⟨join (by decide) b_6_256.down b_6_320.down (by decide)⟩
end Astra247824.HardTail.Batch


namespace Astra247824.HardTail.Slice
private theorem cut_7_128 : rowPrefix 256 - rowPrefix 128 = (622641687 : ℤ) := (tree_interval 7 128).symm.trans Batch.b_7_128.down
private theorem cut_7_256 : rowPrefix 384 - rowPrefix 256 = (262384439 : ℤ) := (tree_interval 7 256).symm.trans Batch.b_7_256.down
theorem verified_slice_3 : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1.H3 := by
  change sourcePrefix 384 - sourcePrefix 128 = 885026126
  rw [prefix_original,prefix_eq,prefix_original,prefix_eq]
  exact (join_intervals cut_7_128 cut_7_256)
end Astra247824.HardTail.Slice
theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1.H3 := Astra247824.HardTail.Slice.verified_slice_3
