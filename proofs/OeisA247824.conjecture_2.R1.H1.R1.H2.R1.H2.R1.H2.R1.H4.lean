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
private def b_2_384 : PLift (tree 2 384 = (5783453 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_388 : PLift (tree 2 388 = (5431241 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_384 : PLift (tree 3 384 = (11214694 : ℤ)) := ⟨join (by decide) b_2_384.down b_2_388.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_392 : PLift (tree 2 392 = (5620764 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_396 : PLift (tree 2 396 = (5553056 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_392 : PLift (tree 3 392 = (11173820 : ℤ)) := ⟨join (by decide) b_2_392.down b_2_396.down (by decide)⟩
private def b_4_384 : PLift (tree 4 384 = (22388514 : ℤ)) := ⟨join (by decide) b_3_384.down b_3_392.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_400 : PLift (tree 2 400 = (5281820 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_404 : PLift (tree 2 404 = (5426365 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_400 : PLift (tree 3 400 = (10708185 : ℤ)) := ⟨join (by decide) b_2_400.down b_2_404.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_408 : PLift (tree 2 408 = (5515397 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_412 : PLift (tree 2 412 = (5414209 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_408 : PLift (tree 3 408 = (10929606 : ℤ)) := ⟨join (by decide) b_2_408.down b_2_412.down (by decide)⟩
private def b_4_400 : PLift (tree 4 400 = (21637791 : ℤ)) := ⟨join (by decide) b_3_400.down b_3_408.down (by decide)⟩
private def b_5_384 : PLift (tree 5 384 = (44026305 : ℤ)) := ⟨join (by decide) b_4_384.down b_4_400.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_416 : PLift (tree 2 416 = (5178243 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_420 : PLift (tree 2 420 = (5043277 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_416 : PLift (tree 3 416 = (10221520 : ℤ)) := ⟨join (by decide) b_2_416.down b_2_420.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_424 : PLift (tree 2 424 = (4948965 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_428 : PLift (tree 2 428 = (5051787 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_424 : PLift (tree 3 424 = (10000752 : ℤ)) := ⟨join (by decide) b_2_424.down b_2_428.down (by decide)⟩
private def b_4_416 : PLift (tree 4 416 = (20222272 : ℤ)) := ⟨join (by decide) b_3_416.down b_3_424.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_432 : PLift (tree 2 432 = (5027931 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_436 : PLift (tree 2 436 = (4802455 : ℤ)) := ⟨by decide +kernel⟩
private def b_3_432 : PLift (tree 3 432 = (9830386 : ℤ)) := ⟨join (by decide) b_2_432.down b_2_436.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_440 : PLift (tree 3 440 = (8987189 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_432 : PLift (tree 4 432 = (18817575 : ℤ)) := ⟨join (by decide) b_3_432.down b_3_440.down (by decide)⟩
private def b_5_416 : PLift (tree 5 416 = (39039847 : ℤ)) := ⟨join (by decide) b_4_416.down b_4_432.down (by decide)⟩
private def b_6_384 : PLift (tree 6 384 = (83066152 : ℤ)) := ⟨join (by decide) b_5_384.down b_5_416.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_448 : PLift (tree 3 448 = (9294894 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_456 : PLift (tree 3 456 = (8596763 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_448 : PLift (tree 4 448 = (17891657 : ℤ)) := ⟨join (by decide) b_3_448.down b_3_456.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_464 : PLift (tree 3 464 = (8549958 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_472 : PLift (tree 3 472 = (8334791 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_464 : PLift (tree 4 464 = (16884749 : ℤ)) := ⟨join (by decide) b_3_464.down b_3_472.down (by decide)⟩
private def b_5_448 : PLift (tree 5 448 = (34776406 : ℤ)) := ⟨join (by decide) b_4_448.down b_4_464.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_480 : PLift (tree 3 480 = (8144330 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_488 : PLift (tree 3 488 = (7994579 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_480 : PLift (tree 4 480 = (16138909 : ℤ)) := ⟨join (by decide) b_3_480.down b_3_488.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_496 : PLift (tree 3 496 = (7732014 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_504 : PLift (tree 3 504 = (7609543 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_496 : PLift (tree 4 496 = (15341557 : ℤ)) := ⟨join (by decide) b_3_496.down b_3_504.down (by decide)⟩
private def b_5_480 : PLift (tree 5 480 = (31480466 : ℤ)) := ⟨join (by decide) b_4_480.down b_4_496.down (by decide)⟩
private def b_6_448 : PLift (tree 6 448 = (66256872 : ℤ)) := ⟨join (by decide) b_5_448.down b_5_480.down (by decide)⟩
def b_7_384 : PLift (tree 7 384 = (149323024 : ℤ)) := ⟨join (by decide) b_6_384.down b_6_448.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_512 : PLift (tree 3 512 = (7244903 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_520 : PLift (tree 3 520 = (7020927 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_512 : PLift (tree 4 512 = (14265830 : ℤ)) := ⟨join (by decide) b_3_512.down b_3_520.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_528 : PLift (tree 3 528 = (6865893 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_536 : PLift (tree 3 536 = (6709645 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_528 : PLift (tree 4 528 = (13575538 : ℤ)) := ⟨join (by decide) b_3_528.down b_3_536.down (by decide)⟩
private def b_5_512 : PLift (tree 5 512 = (27841368 : ℤ)) := ⟨join (by decide) b_4_512.down b_4_528.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_544 : PLift (tree 3 544 = (6662373 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_552 : PLift (tree 3 552 = (6375489 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_544 : PLift (tree 4 544 = (13037862 : ℤ)) := ⟨join (by decide) b_3_544.down b_3_552.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_560 : PLift (tree 3 560 = (6481018 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_568 : PLift (tree 3 568 = (6050348 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_560 : PLift (tree 4 560 = (12531366 : ℤ)) := ⟨join (by decide) b_3_560.down b_3_568.down (by decide)⟩
private def b_5_544 : PLift (tree 5 544 = (25569228 : ℤ)) := ⟨join (by decide) b_4_544.down b_4_560.down (by decide)⟩
private def b_6_512 : PLift (tree 6 512 = (53410596 : ℤ)) := ⟨join (by decide) b_5_512.down b_5_544.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_576 : PLift (tree 3 576 = (5819479 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_584 : PLift (tree 3 584 = (5619415 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_576 : PLift (tree 4 576 = (11438894 : ℤ)) := ⟨join (by decide) b_3_576.down b_3_584.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_592 : PLift (tree 3 592 = (5545869 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_600 : PLift (tree 3 600 = (5404064 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_592 : PLift (tree 4 592 = (10949933 : ℤ)) := ⟨join (by decide) b_3_592.down b_3_600.down (by decide)⟩
private def b_5_576 : PLift (tree 5 576 = (22388827 : ℤ)) := ⟨join (by decide) b_4_576.down b_4_592.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_608 : PLift (tree 3 608 = (5464648 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_616 : PLift (tree 3 616 = (5253091 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_608 : PLift (tree 4 608 = (10717739 : ℤ)) := ⟨join (by decide) b_3_608.down b_3_616.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_624 : PLift (tree 3 624 = (5410502 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_632 : PLift (tree 3 632 = (5255247 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_624 : PLift (tree 4 624 = (10665749 : ℤ)) := ⟨join (by decide) b_3_624.down b_3_632.down (by decide)⟩
private def b_5_608 : PLift (tree 5 608 = (21383488 : ℤ)) := ⟨join (by decide) b_4_608.down b_4_624.down (by decide)⟩
private def b_6_576 : PLift (tree 6 576 = (43772315 : ℤ)) := ⟨join (by decide) b_5_576.down b_5_608.down (by decide)⟩
private def b_7_512 : PLift (tree 7 512 = (97182911 : ℤ)) := ⟨join (by decide) b_6_512.down b_6_576.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_640 : PLift (tree 3 640 = (4727973 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_648 : PLift (tree 3 648 = (4949826 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_640 : PLift (tree 4 640 = (9677799 : ℤ)) := ⟨join (by decide) b_3_640.down b_3_648.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_656 : PLift (tree 3 656 = (4738079 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_664 : PLift (tree 3 664 = (4685476 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_656 : PLift (tree 4 656 = (9423555 : ℤ)) := ⟨join (by decide) b_3_656.down b_3_664.down (by decide)⟩
private def b_5_640 : PLift (tree 5 640 = (19101354 : ℤ)) := ⟨join (by decide) b_4_640.down b_4_656.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_672 : PLift (tree 3 672 = (4515832 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_3_680 : PLift (tree 3 680 = (4519125 : ℤ)) := ⟨by decide +kernel⟩
private def b_4_672 : PLift (tree 4 672 = (9034957 : ℤ)) := ⟨join (by decide) b_3_672.down b_3_680.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_688 : PLift (tree 4 688 = (8451685 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_672 : PLift (tree 5 672 = (17486642 : ℤ)) := ⟨join (by decide) b_4_672.down b_4_688.down (by decide)⟩
private def b_6_640 : PLift (tree 6 640 = (36587996 : ℤ)) := ⟨join (by decide) b_5_640.down b_5_672.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_704 : PLift (tree 4 704 = (8878706 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_720 : PLift (tree 4 720 = (8097887 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_704 : PLift (tree 5 704 = (16976593 : ℤ)) := ⟨join (by decide) b_4_704.down b_4_720.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_736 : PLift (tree 4 736 = (7855395 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_752 : PLift (tree 4 752 = (7417316 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_736 : PLift (tree 5 736 = (15272711 : ℤ)) := ⟨join (by decide) b_4_736.down b_4_752.down (by decide)⟩
private def b_6_704 : PLift (tree 6 704 = (32249304 : ℤ)) := ⟨join (by decide) b_5_704.down b_5_736.down (by decide)⟩
private def b_7_640 : PLift (tree 7 640 = (68837300 : ℤ)) := ⟨join (by decide) b_6_640.down b_6_704.down (by decide)⟩
def b_8_512 : PLift (tree 8 512 = (166020211 : ℤ)) := ⟨join (by decide) b_7_512.down b_7_640.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_768 : PLift (tree 4 768 = (7332138 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_784 : PLift (tree 4 784 = (7328384 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_768 : PLift (tree 5 768 = (14660522 : ℤ)) := ⟨join (by decide) b_4_768.down b_4_784.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_800 : PLift (tree 4 800 = (6896632 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_816 : PLift (tree 4 816 = (6542256 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_800 : PLift (tree 5 800 = (13438888 : ℤ)) := ⟨join (by decide) b_4_800.down b_4_816.down (by decide)⟩
private def b_6_768 : PLift (tree 6 768 = (28099410 : ℤ)) := ⟨join (by decide) b_5_768.down b_5_800.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_832 : PLift (tree 4 832 = (6219838 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_848 : PLift (tree 4 848 = (6113750 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_832 : PLift (tree 5 832 = (12333588 : ℤ)) := ⟨join (by decide) b_4_832.down b_4_848.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_864 : PLift (tree 4 864 = (5617863 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_880 : PLift (tree 4 880 = (5692663 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_864 : PLift (tree 5 864 = (11310526 : ℤ)) := ⟨join (by decide) b_4_864.down b_4_880.down (by decide)⟩
private def b_6_832 : PLift (tree 6 832 = (23644114 : ℤ)) := ⟨join (by decide) b_5_832.down b_5_864.down (by decide)⟩
private def b_7_768 : PLift (tree 7 768 = (51743524 : ℤ)) := ⟨join (by decide) b_6_768.down b_6_832.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_896 : PLift (tree 4 896 = (5541950 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_912 : PLift (tree 4 912 = (5455412 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_896 : PLift (tree 5 896 = (10997362 : ℤ)) := ⟨join (by decide) b_4_896.down b_4_912.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_928 : PLift (tree 4 928 = (5174164 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_944 : PLift (tree 4 944 = (5416535 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_928 : PLift (tree 5 928 = (10590699 : ℤ)) := ⟨join (by decide) b_4_928.down b_4_944.down (by decide)⟩
private def b_6_896 : PLift (tree 6 896 = (21588061 : ℤ)) := ⟨join (by decide) b_5_896.down b_5_928.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_960 : PLift (tree 4 960 = (5062525 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_976 : PLift (tree 4 976 = (4943243 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_960 : PLift (tree 5 960 = (10005768 : ℤ)) := ⟨join (by decide) b_4_960.down b_4_976.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_992 : PLift (tree 4 992 = (4611485 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_1008 : PLift (tree 4 1008 = (4928547 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_992 : PLift (tree 5 992 = (9540032 : ℤ)) := ⟨join (by decide) b_4_992.down b_4_1008.down (by decide)⟩
private def b_6_960 : PLift (tree 6 960 = (19545800 : ℤ)) := ⟨join (by decide) b_5_960.down b_5_992.down (by decide)⟩
private def b_7_896 : PLift (tree 7 896 = (41133861 : ℤ)) := ⟨join (by decide) b_6_896.down b_6_960.down (by decide)⟩
def b_8_768 : PLift (tree 8 768 = (92877385 : ℤ)) := ⟨join (by decide) b_7_768.down b_7_896.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_1024 : PLift (tree 4 1024 = (4810400 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_4_1040 : PLift (tree 4 1040 = (4397280 : ℤ)) := ⟨by decide +kernel⟩
private def b_5_1024 : PLift (tree 5 1024 = (9207680 : ℤ)) := ⟨join (by decide) b_4_1024.down b_4_1040.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1056 : PLift (tree 5 1056 = (8080743 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1024 : PLift (tree 6 1024 = (17288423 : ℤ)) := ⟨join (by decide) b_5_1024.down b_5_1056.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1088 : PLift (tree 5 1088 = (8014179 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1120 : PLift (tree 5 1120 = (7319947 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1088 : PLift (tree 6 1088 = (15334126 : ℤ)) := ⟨join (by decide) b_5_1088.down b_5_1120.down (by decide)⟩
private def b_7_1024 : PLift (tree 7 1024 = (32622549 : ℤ)) := ⟨join (by decide) b_6_1024.down b_6_1088.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1152 : PLift (tree 5 1152 = (7239148 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1184 : PLift (tree 5 1184 = (6946780 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1152 : PLift (tree 6 1152 = (14185928 : ℤ)) := ⟨join (by decide) b_5_1152.down b_5_1184.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1216 : PLift (tree 5 1216 = (6206900 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1248 : PLift (tree 5 1248 = (6162284 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1216 : PLift (tree 6 1216 = (12369184 : ℤ)) := ⟨join (by decide) b_5_1216.down b_5_1248.down (by decide)⟩
private def b_7_1152 : PLift (tree 7 1152 = (26555112 : ℤ)) := ⟨join (by decide) b_6_1152.down b_6_1216.down (by decide)⟩
private def b_8_1024 : PLift (tree 8 1024 = (59177661 : ℤ)) := ⟨join (by decide) b_7_1024.down b_7_1152.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1280 : PLift (tree 5 1280 = (5812129 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1312 : PLift (tree 5 1312 = (5734405 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1280 : PLift (tree 6 1280 = (11546534 : ℤ)) := ⟨join (by decide) b_5_1280.down b_5_1312.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1344 : PLift (tree 5 1344 = (5105759 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1376 : PLift (tree 5 1376 = (5187396 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1344 : PLift (tree 6 1344 = (10293155 : ℤ)) := ⟨join (by decide) b_5_1344.down b_5_1376.down (by decide)⟩
private def b_7_1280 : PLift (tree 7 1280 = (21839689 : ℤ)) := ⟨join (by decide) b_6_1280.down b_6_1344.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1408 : PLift (tree 5 1408 = (4879652 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_5_1440 : PLift (tree 5 1440 = (4545829 : ℤ)) := ⟨by decide +kernel⟩
private def b_6_1408 : PLift (tree 6 1408 = (9425481 : ℤ)) := ⟨join (by decide) b_5_1408.down b_5_1440.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1472 : PLift (tree 6 1472 = (8729947 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_1408 : PLift (tree 7 1408 = (18155428 : ℤ)) := ⟨join (by decide) b_6_1408.down b_6_1472.down (by decide)⟩
private def b_8_1280 : PLift (tree 8 1280 = (39995117 : ℤ)) := ⟨join (by decide) b_7_1280.down b_7_1408.down (by decide)⟩
private def b_9_1024 : PLift (tree 9 1024 = (99172778 : ℤ)) := ⟨join (by decide) b_8_1024.down b_8_1280.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1536 : PLift (tree 6 1536 = (8171117 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1600 : PLift (tree 6 1600 = (7304720 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_1536 : PLift (tree 7 1536 = (15475837 : ℤ)) := ⟨join (by decide) b_6_1536.down b_6_1600.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1664 : PLift (tree 6 1664 = (6906530 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1728 : PLift (tree 6 1728 = (6445616 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_1664 : PLift (tree 7 1664 = (13352146 : ℤ)) := ⟨join (by decide) b_6_1664.down b_6_1728.down (by decide)⟩
private def b_8_1536 : PLift (tree 8 1536 = (28827983 : ℤ)) := ⟨join (by decide) b_7_1536.down b_7_1664.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1792 : PLift (tree 6 1792 = (6108057 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1856 : PLift (tree 6 1856 = (5774912 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_1792 : PLift (tree 7 1792 = (11882969 : ℤ)) := ⟨join (by decide) b_6_1792.down b_6_1856.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1920 : PLift (tree 6 1920 = (5409844 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_1984 : PLift (tree 6 1984 = (5156205 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_1920 : PLift (tree 7 1920 = (10566049 : ℤ)) := ⟨join (by decide) b_6_1920.down b_6_1984.down (by decide)⟩
private def b_8_1792 : PLift (tree 8 1792 = (22449018 : ℤ)) := ⟨join (by decide) b_7_1792.down b_7_1920.down (by decide)⟩
private def b_9_1536 : PLift (tree 9 1536 = (51277001 : ℤ)) := ⟨join (by decide) b_8_1536.down b_8_1792.down (by decide)⟩
def b_10_1024 : PLift (tree 10 1024 = (150449779 : ℤ)) := ⟨join (by decide) b_9_1024.down b_9_1536.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2048 : PLift (tree 6 2048 = (4750656 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2112 : PLift (tree 6 2112 = (4401507 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2048 : PLift (tree 7 2048 = (9152163 : ℤ)) := ⟨join (by decide) b_6_2048.down b_6_2112.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2176 : PLift (tree 6 2176 = (4352865 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2240 : PLift (tree 6 2240 = (3786924 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2176 : PLift (tree 7 2176 = (8139789 : ℤ)) := ⟨join (by decide) b_6_2176.down b_6_2240.down (by decide)⟩
private def b_8_2048 : PLift (tree 8 2048 = (17291952 : ℤ)) := ⟨join (by decide) b_7_2048.down b_7_2176.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2304 : PLift (tree 6 2304 = (3918370 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2368 : PLift (tree 6 2368 = (3508515 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2304 : PLift (tree 7 2304 = (7426885 : ℤ)) := ⟨join (by decide) b_6_2304.down b_6_2368.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2432 : PLift (tree 6 2432 = (3376035 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2496 : PLift (tree 6 2496 = (3178403 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2432 : PLift (tree 7 2432 = (6554438 : ℤ)) := ⟨join (by decide) b_6_2432.down b_6_2496.down (by decide)⟩
private def b_8_2304 : PLift (tree 8 2304 = (13981323 : ℤ)) := ⟨join (by decide) b_7_2304.down b_7_2432.down (by decide)⟩
private def b_9_2048 : PLift (tree 9 2048 = (31273275 : ℤ)) := ⟨join (by decide) b_8_2048.down b_8_2304.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2560 : PLift (tree 6 2560 = (3182531 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2624 : PLift (tree 6 2624 = (2856599 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2560 : PLift (tree 7 2560 = (6039130 : ℤ)) := ⟨join (by decide) b_6_2560.down b_6_2624.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2688 : PLift (tree 6 2688 = (3036600 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2752 : PLift (tree 6 2752 = (2643438 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2688 : PLift (tree 7 2688 = (5680038 : ℤ)) := ⟨join (by decide) b_6_2688.down b_6_2752.down (by decide)⟩
private def b_8_2560 : PLift (tree 8 2560 = (11719168 : ℤ)) := ⟨join (by decide) b_7_2560.down b_7_2688.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2816 : PLift (tree 6 2816 = (2592862 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2880 : PLift (tree 6 2880 = (2405642 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2816 : PLift (tree 7 2816 = (4998504 : ℤ)) := ⟨join (by decide) b_6_2816.down b_6_2880.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_2944 : PLift (tree 6 2944 = (2326562 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3008 : PLift (tree 6 3008 = (2281035 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_2944 : PLift (tree 7 2944 = (4607597 : ℤ)) := ⟨join (by decide) b_6_2944.down b_6_3008.down (by decide)⟩
private def b_8_2816 : PLift (tree 8 2816 = (9606101 : ℤ)) := ⟨join (by decide) b_7_2816.down b_7_2944.down (by decide)⟩
private def b_9_2560 : PLift (tree 9 2560 = (21325269 : ℤ)) := ⟨join (by decide) b_8_2560.down b_8_2816.down (by decide)⟩
private def b_10_2048 : PLift (tree 10 2048 = (52598544 : ℤ)) := ⟨join (by decide) b_9_2048.down b_9_2560.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3072 : PLift (tree 6 3072 = (2287902 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3136 : PLift (tree 6 3136 = (2047469 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3072 : PLift (tree 7 3072 = (4335371 : ℤ)) := ⟨join (by decide) b_6_3072.down b_6_3136.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3200 : PLift (tree 6 3200 = (2227883 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3264 : PLift (tree 6 3264 = (1955174 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3200 : PLift (tree 7 3200 = (4183057 : ℤ)) := ⟨join (by decide) b_6_3200.down b_6_3264.down (by decide)⟩
private def b_8_3072 : PLift (tree 8 3072 = (8518428 : ℤ)) := ⟨join (by decide) b_7_3072.down b_7_3200.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3328 : PLift (tree 6 3328 = (2002108 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3392 : PLift (tree 6 3392 = (1786913 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3328 : PLift (tree 7 3328 = (3789021 : ℤ)) := ⟨join (by decide) b_6_3328.down b_6_3392.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3456 : PLift (tree 6 3456 = (1963396 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3520 : PLift (tree 6 3520 = (1610774 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3456 : PLift (tree 7 3456 = (3574170 : ℤ)) := ⟨join (by decide) b_6_3456.down b_6_3520.down (by decide)⟩
private def b_8_3328 : PLift (tree 8 3328 = (7363191 : ℤ)) := ⟨join (by decide) b_7_3328.down b_7_3456.down (by decide)⟩
private def b_9_3072 : PLift (tree 9 3072 = (15881619 : ℤ)) := ⟨join (by decide) b_8_3072.down b_8_3328.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3584 : PLift (tree 6 3584 = (1637033 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3648 : PLift (tree 6 3648 = (1517776 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3584 : PLift (tree 7 3584 = (3154809 : ℤ)) := ⟨join (by decide) b_6_3584.down b_6_3648.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3712 : PLift (tree 6 3712 = (1527424 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3776 : PLift (tree 6 3776 = (1439179 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3712 : PLift (tree 7 3712 = (2966603 : ℤ)) := ⟨join (by decide) b_6_3712.down b_6_3776.down (by decide)⟩
private def b_8_3584 : PLift (tree 8 3584 = (6121412 : ℤ)) := ⟨join (by decide) b_7_3584.down b_7_3712.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3840 : PLift (tree 6 3840 = (1435576 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3904 : PLift (tree 6 3904 = (1366255 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3840 : PLift (tree 7 3840 = (2801831 : ℤ)) := ⟨join (by decide) b_6_3840.down b_6_3904.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_3968 : PLift (tree 6 3968 = (1400079 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4032 : PLift (tree 6 4032 = (1363949 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_3968 : PLift (tree 7 3968 = (2764028 : ℤ)) := ⟨join (by decide) b_6_3968.down b_6_4032.down (by decide)⟩
private def b_8_3840 : PLift (tree 8 3840 = (5565859 : ℤ)) := ⟨join (by decide) b_7_3840.down b_7_3968.down (by decide)⟩
private def b_9_3584 : PLift (tree 9 3584 = (11687271 : ℤ)) := ⟨join (by decide) b_8_3584.down b_8_3840.down (by decide)⟩
private def b_10_3072 : PLift (tree 10 3072 = (27568890 : ℤ)) := ⟨join (by decide) b_9_3072.down b_9_3584.down (by decide)⟩
def b_11_2048 : PLift (tree 11 2048 = (80167434 : ℤ)) := ⟨join (by decide) b_10_2048.down b_10_3072.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4096 : PLift (tree 6 4096 = (1218021 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4160 : PLift (tree 6 4160 = (1230353 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4096 : PLift (tree 7 4096 = (2448374 : ℤ)) := ⟨join (by decide) b_6_4096.down b_6_4160.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4224 : PLift (tree 6 4224 = (1384097 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4288 : PLift (tree 6 4288 = (1125675 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4224 : PLift (tree 7 4224 = (2509772 : ℤ)) := ⟨join (by decide) b_6_4224.down b_6_4288.down (by decide)⟩
private def b_8_4096 : PLift (tree 8 4096 = (4958146 : ℤ)) := ⟨join (by decide) b_7_4096.down b_7_4224.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4352 : PLift (tree 6 4352 = (1188131 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4416 : PLift (tree 6 4416 = (1088376 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4352 : PLift (tree 7 4352 = (2276507 : ℤ)) := ⟨join (by decide) b_6_4352.down b_6_4416.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4480 : PLift (tree 6 4480 = (1026517 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4544 : PLift (tree 6 4544 = (1060433 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4480 : PLift (tree 7 4480 = (2086950 : ℤ)) := ⟨join (by decide) b_6_4480.down b_6_4544.down (by decide)⟩
private def b_8_4352 : PLift (tree 8 4352 = (4363457 : ℤ)) := ⟨join (by decide) b_7_4352.down b_7_4480.down (by decide)⟩
private def b_9_4096 : PLift (tree 9 4096 = (9321603 : ℤ)) := ⟨join (by decide) b_8_4096.down b_8_4352.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4608 : PLift (tree 6 4608 = (1011137 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4672 : PLift (tree 6 4672 = (933245 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4608 : PLift (tree 7 4608 = (1944382 : ℤ)) := ⟨join (by decide) b_6_4608.down b_6_4672.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4736 : PLift (tree 6 4736 = (967094 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4800 : PLift (tree 6 4800 = (942247 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4736 : PLift (tree 7 4736 = (1909341 : ℤ)) := ⟨join (by decide) b_6_4736.down b_6_4800.down (by decide)⟩
private def b_8_4608 : PLift (tree 8 4608 = (3853723 : ℤ)) := ⟨join (by decide) b_7_4608.down b_7_4736.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4864 : PLift (tree 6 4864 = (909386 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4928 : PLift (tree 6 4928 = (956871 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4864 : PLift (tree 7 4864 = (1866257 : ℤ)) := ⟨join (by decide) b_6_4864.down b_6_4928.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_4992 : PLift (tree 6 4992 = (785956 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5056 : PLift (tree 6 5056 = (821146 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_4992 : PLift (tree 7 4992 = (1607102 : ℤ)) := ⟨join (by decide) b_6_4992.down b_6_5056.down (by decide)⟩
private def b_8_4864 : PLift (tree 8 4864 = (3473359 : ℤ)) := ⟨join (by decide) b_7_4864.down b_7_4992.down (by decide)⟩
private def b_9_4608 : PLift (tree 9 4608 = (7327082 : ℤ)) := ⟨join (by decide) b_8_4608.down b_8_4864.down (by decide)⟩
private def b_10_4096 : PLift (tree 10 4096 = (16648685 : ℤ)) := ⟨join (by decide) b_9_4096.down b_9_4608.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5120 : PLift (tree 6 5120 = (744921 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5184 : PLift (tree 6 5184 = (827657 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5120 : PLift (tree 7 5120 = (1572578 : ℤ)) := ⟨join (by decide) b_6_5120.down b_6_5184.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5248 : PLift (tree 6 5248 = (834261 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5312 : PLift (tree 6 5312 = (838448 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5248 : PLift (tree 7 5248 = (1672709 : ℤ)) := ⟨join (by decide) b_6_5248.down b_6_5312.down (by decide)⟩
private def b_8_5120 : PLift (tree 8 5120 = (3245287 : ℤ)) := ⟨join (by decide) b_7_5120.down b_7_5248.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5376 : PLift (tree 6 5376 = (735235 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5440 : PLift (tree 6 5440 = (714275 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5376 : PLift (tree 7 5376 = (1449510 : ℤ)) := ⟨join (by decide) b_6_5376.down b_6_5440.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5504 : PLift (tree 6 5504 = (688140 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5568 : PLift (tree 6 5568 = (671060 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5504 : PLift (tree 7 5504 = (1359200 : ℤ)) := ⟨join (by decide) b_6_5504.down b_6_5568.down (by decide)⟩
private def b_8_5376 : PLift (tree 8 5376 = (2808710 : ℤ)) := ⟨join (by decide) b_7_5376.down b_7_5504.down (by decide)⟩
private def b_9_5120 : PLift (tree 9 5120 = (6053997 : ℤ)) := ⟨join (by decide) b_8_5120.down b_8_5376.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5632 : PLift (tree 6 5632 = (682315 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5696 : PLift (tree 6 5696 = (747700 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5632 : PLift (tree 7 5632 = (1430015 : ℤ)) := ⟨join (by decide) b_6_5632.down b_6_5696.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5760 : PLift (tree 6 5760 = (759999 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5824 : PLift (tree 6 5824 = (692038 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5760 : PLift (tree 7 5760 = (1452037 : ℤ)) := ⟨join (by decide) b_6_5760.down b_6_5824.down (by decide)⟩
private def b_8_5632 : PLift (tree 8 5632 = (2882052 : ℤ)) := ⟨join (by decide) b_7_5632.down b_7_5760.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5888 : PLift (tree 6 5888 = (573212 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_5952 : PLift (tree 6 5952 = (511575 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_5888 : PLift (tree 7 5888 = (1084787 : ℤ)) := ⟨join (by decide) b_6_5888.down b_6_5952.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6016 : PLift (tree 6 6016 = (586663 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6080 : PLift (tree 6 6080 = (650290 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6016 : PLift (tree 7 6016 = (1236953 : ℤ)) := ⟨join (by decide) b_6_6016.down b_6_6080.down (by decide)⟩
private def b_8_5888 : PLift (tree 8 5888 = (2321740 : ℤ)) := ⟨join (by decide) b_7_5888.down b_7_6016.down (by decide)⟩
private def b_9_5632 : PLift (tree 9 5632 = (5203792 : ℤ)) := ⟨join (by decide) b_8_5632.down b_8_5888.down (by decide)⟩
private def b_10_5120 : PLift (tree 10 5120 = (11257789 : ℤ)) := ⟨join (by decide) b_9_5120.down b_9_5632.down (by decide)⟩
def b_11_4096 : PLift (tree 11 4096 = (27906474 : ℤ)) := ⟨join (by decide) b_10_4096.down b_10_5120.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6144 : PLift (tree 6 6144 = (545344 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6208 : PLift (tree 6 6208 = (598844 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6144 : PLift (tree 7 6144 = (1144188 : ℤ)) := ⟨join (by decide) b_6_6144.down b_6_6208.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6272 : PLift (tree 6 6272 = (511765 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6336 : PLift (tree 6 6336 = (577484 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6272 : PLift (tree 7 6272 = (1089249 : ℤ)) := ⟨join (by decide) b_6_6272.down b_6_6336.down (by decide)⟩
private def b_8_6144 : PLift (tree 8 6144 = (2233437 : ℤ)) := ⟨join (by decide) b_7_6144.down b_7_6272.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6400 : PLift (tree 6 6400 = (591255 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6464 : PLift (tree 6 6464 = (553812 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6400 : PLift (tree 7 6400 = (1145067 : ℤ)) := ⟨join (by decide) b_6_6400.down b_6_6464.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6528 : PLift (tree 6 6528 = (484170 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6592 : PLift (tree 6 6592 = (535156 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6528 : PLift (tree 7 6528 = (1019326 : ℤ)) := ⟨join (by decide) b_6_6528.down b_6_6592.down (by decide)⟩
private def b_8_6400 : PLift (tree 8 6400 = (2164393 : ℤ)) := ⟨join (by decide) b_7_6400.down b_7_6528.down (by decide)⟩
private def b_9_6144 : PLift (tree 9 6144 = (4397830 : ℤ)) := ⟨join (by decide) b_8_6144.down b_8_6400.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6656 : PLift (tree 6 6656 = (431985 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6720 : PLift (tree 6 6720 = (489180 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6656 : PLift (tree 7 6656 = (921165 : ℤ)) := ⟨join (by decide) b_6_6656.down b_6_6720.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6784 : PLift (tree 6 6784 = (468085 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6848 : PLift (tree 6 6848 = (528883 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6784 : PLift (tree 7 6784 = (996968 : ℤ)) := ⟨join (by decide) b_6_6784.down b_6_6848.down (by decide)⟩
private def b_8_6656 : PLift (tree 8 6656 = (1918133 : ℤ)) := ⟨join (by decide) b_7_6656.down b_7_6784.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6912 : PLift (tree 6 6912 = (364735 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_6976 : PLift (tree 6 6976 = (508493 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_6912 : PLift (tree 7 6912 = (873228 : ℤ)) := ⟨join (by decide) b_6_6912.down b_6_6976.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7040 : PLift (tree 6 7040 = (347034 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7104 : PLift (tree 6 7104 = (451395 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7040 : PLift (tree 7 7040 = (798429 : ℤ)) := ⟨join (by decide) b_6_7040.down b_6_7104.down (by decide)⟩
private def b_8_6912 : PLift (tree 8 6912 = (1671657 : ℤ)) := ⟨join (by decide) b_7_6912.down b_7_7040.down (by decide)⟩
private def b_9_6656 : PLift (tree 9 6656 = (3589790 : ℤ)) := ⟨join (by decide) b_8_6656.down b_8_6912.down (by decide)⟩
private def b_10_6144 : PLift (tree 10 6144 = (7987620 : ℤ)) := ⟨join (by decide) b_9_6144.down b_9_6656.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7168 : PLift (tree 6 7168 = (394362 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7232 : PLift (tree 6 7232 = (388374 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7168 : PLift (tree 7 7168 = (782736 : ℤ)) := ⟨join (by decide) b_6_7168.down b_6_7232.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7296 : PLift (tree 6 7296 = (458845 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7360 : PLift (tree 6 7360 = (437328 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7296 : PLift (tree 7 7296 = (896173 : ℤ)) := ⟨join (by decide) b_6_7296.down b_6_7360.down (by decide)⟩
private def b_8_7168 : PLift (tree 8 7168 = (1678909 : ℤ)) := ⟨join (by decide) b_7_7168.down b_7_7296.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7424 : PLift (tree 6 7424 = (412690 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7488 : PLift (tree 6 7488 = (423361 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7424 : PLift (tree 7 7424 = (836051 : ℤ)) := ⟨join (by decide) b_6_7424.down b_6_7488.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7552 : PLift (tree 6 7552 = (459622 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7616 : PLift (tree 6 7616 = (358386 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7552 : PLift (tree 7 7552 = (818008 : ℤ)) := ⟨join (by decide) b_6_7552.down b_6_7616.down (by decide)⟩
private def b_8_7424 : PLift (tree 8 7424 = (1654059 : ℤ)) := ⟨join (by decide) b_7_7424.down b_7_7552.down (by decide)⟩
private def b_9_7168 : PLift (tree 9 7168 = (3332968 : ℤ)) := ⟨join (by decide) b_8_7168.down b_8_7424.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7680 : PLift (tree 6 7680 = (459423 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7744 : PLift (tree 6 7744 = (313232 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7680 : PLift (tree 7 7680 = (772655 : ℤ)) := ⟨join (by decide) b_6_7680.down b_6_7744.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7808 : PLift (tree 6 7808 = (388527 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7872 : PLift (tree 6 7872 = (389033 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7808 : PLift (tree 7 7808 = (777560 : ℤ)) := ⟨join (by decide) b_6_7808.down b_6_7872.down (by decide)⟩
private def b_8_7680 : PLift (tree 8 7680 = (1550215 : ℤ)) := ⟨join (by decide) b_7_7680.down b_7_7808.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_7936 : PLift (tree 6 7936 = (413479 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8000 : PLift (tree 6 8000 = (320996 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_7936 : PLift (tree 7 7936 = (734475 : ℤ)) := ⟨join (by decide) b_6_7936.down b_6_8000.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8064 : PLift (tree 6 8064 = (372537 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8128 : PLift (tree 6 8128 = (369547 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8064 : PLift (tree 7 8064 = (742084 : ℤ)) := ⟨join (by decide) b_6_8064.down b_6_8128.down (by decide)⟩
private def b_8_7936 : PLift (tree 8 7936 = (1476559 : ℤ)) := ⟨join (by decide) b_7_7936.down b_7_8064.down (by decide)⟩
private def b_9_7680 : PLift (tree 9 7680 = (3026774 : ℤ)) := ⟨join (by decide) b_8_7680.down b_8_7936.down (by decide)⟩
private def b_10_7168 : PLift (tree 10 7168 = (6359742 : ℤ)) := ⟨join (by decide) b_9_7168.down b_9_7680.down (by decide)⟩
def b_11_6144 : PLift (tree 11 6144 = (14347362 : ℤ)) := ⟨join (by decide) b_10_6144.down b_10_7168.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8192 : PLift (tree 6 8192 = (316025 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8256 : PLift (tree 6 8256 = (299663 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8192 : PLift (tree 7 8192 = (615688 : ℤ)) := ⟨join (by decide) b_6_8192.down b_6_8256.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8320 : PLift (tree 6 8320 = (327947 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8384 : PLift (tree 6 8384 = (335763 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8320 : PLift (tree 7 8320 = (663710 : ℤ)) := ⟨join (by decide) b_6_8320.down b_6_8384.down (by decide)⟩
private def b_8_8192 : PLift (tree 8 8192 = (1279398 : ℤ)) := ⟨join (by decide) b_7_8192.down b_7_8320.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8448 : PLift (tree 6 8448 = (291980 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8512 : PLift (tree 6 8512 = (286841 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8448 : PLift (tree 7 8448 = (578821 : ℤ)) := ⟨join (by decide) b_6_8448.down b_6_8512.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8576 : PLift (tree 6 8576 = (353915 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8640 : PLift (tree 6 8640 = (332505 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8576 : PLift (tree 7 8576 = (686420 : ℤ)) := ⟨join (by decide) b_6_8576.down b_6_8640.down (by decide)⟩
private def b_8_8448 : PLift (tree 8 8448 = (1265241 : ℤ)) := ⟨join (by decide) b_7_8448.down b_7_8576.down (by decide)⟩
private def b_9_8192 : PLift (tree 9 8192 = (2544639 : ℤ)) := ⟨join (by decide) b_8_8192.down b_8_8448.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8704 : PLift (tree 6 8704 = (347713 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8768 : PLift (tree 6 8768 = (301219 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8704 : PLift (tree 7 8704 = (648932 : ℤ)) := ⟨join (by decide) b_6_8704.down b_6_8768.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8832 : PLift (tree 6 8832 = (241179 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8896 : PLift (tree 6 8896 = (258199 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8832 : PLift (tree 7 8832 = (499378 : ℤ)) := ⟨join (by decide) b_6_8832.down b_6_8896.down (by decide)⟩
private def b_8_8704 : PLift (tree 8 8704 = (1148310 : ℤ)) := ⟨join (by decide) b_7_8704.down b_7_8832.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_8960 : PLift (tree 6 8960 = (310308 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9024 : PLift (tree 6 9024 = (297155 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_8960 : PLift (tree 7 8960 = (607463 : ℤ)) := ⟨join (by decide) b_6_8960.down b_6_9024.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9088 : PLift (tree 6 9088 = (257745 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9152 : PLift (tree 6 9152 = (224572 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9088 : PLift (tree 7 9088 = (482317 : ℤ)) := ⟨join (by decide) b_6_9088.down b_6_9152.down (by decide)⟩
private def b_8_8960 : PLift (tree 8 8960 = (1089780 : ℤ)) := ⟨join (by decide) b_7_8960.down b_7_9088.down (by decide)⟩
private def b_9_8704 : PLift (tree 9 8704 = (2238090 : ℤ)) := ⟨join (by decide) b_8_8704.down b_8_8960.down (by decide)⟩
private def b_10_8192 : PLift (tree 10 8192 = (4782729 : ℤ)) := ⟨join (by decide) b_9_8192.down b_9_8704.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9216 : PLift (tree 6 9216 = (308129 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9280 : PLift (tree 6 9280 = (249015 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9216 : PLift (tree 7 9216 = (557144 : ℤ)) := ⟨join (by decide) b_6_9216.down b_6_9280.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9344 : PLift (tree 6 9344 = (270351 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9408 : PLift (tree 6 9408 = (286204 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9344 : PLift (tree 7 9344 = (556555 : ℤ)) := ⟨join (by decide) b_6_9344.down b_6_9408.down (by decide)⟩
private def b_8_9216 : PLift (tree 8 9216 = (1113699 : ℤ)) := ⟨join (by decide) b_7_9216.down b_7_9344.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9472 : PLift (tree 6 9472 = (255073 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9536 : PLift (tree 6 9536 = (289515 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9472 : PLift (tree 7 9472 = (544588 : ℤ)) := ⟨join (by decide) b_6_9472.down b_6_9536.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9600 : PLift (tree 6 9600 = (199392 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9664 : PLift (tree 6 9664 = (217562 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9600 : PLift (tree 7 9600 = (416954 : ℤ)) := ⟨join (by decide) b_6_9600.down b_6_9664.down (by decide)⟩
private def b_8_9472 : PLift (tree 8 9472 = (961542 : ℤ)) := ⟨join (by decide) b_7_9472.down b_7_9600.down (by decide)⟩
private def b_9_9216 : PLift (tree 9 9216 = (2075241 : ℤ)) := ⟨join (by decide) b_8_9216.down b_8_9472.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9728 : PLift (tree 6 9728 = (251953 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9792 : PLift (tree 6 9792 = (227855 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9728 : PLift (tree 7 9728 = (479808 : ℤ)) := ⟨join (by decide) b_6_9728.down b_6_9792.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9856 : PLift (tree 6 9856 = (287751 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9920 : PLift (tree 6 9920 = (213971 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9856 : PLift (tree 7 9856 = (501722 : ℤ)) := ⟨join (by decide) b_6_9856.down b_6_9920.down (by decide)⟩
private def b_8_9728 : PLift (tree 8 9728 = (981530 : ℤ)) := ⟨join (by decide) b_7_9728.down b_7_9856.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_9984 : PLift (tree 6 9984 = (221265 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10048 : PLift (tree 6 10048 = (268377 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_9984 : PLift (tree 7 9984 = (489642 : ℤ)) := ⟨join (by decide) b_6_9984.down b_6_10048.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10112 : PLift (tree 6 10112 = (255393 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10176 : PLift (tree 6 10176 = (170884 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10112 : PLift (tree 7 10112 = (426277 : ℤ)) := ⟨join (by decide) b_6_10112.down b_6_10176.down (by decide)⟩
private def b_8_9984 : PLift (tree 8 9984 = (915919 : ℤ)) := ⟨join (by decide) b_7_9984.down b_7_10112.down (by decide)⟩
private def b_9_9728 : PLift (tree 9 9728 = (1897449 : ℤ)) := ⟨join (by decide) b_8_9728.down b_8_9984.down (by decide)⟩
private def b_10_9216 : PLift (tree 10 9216 = (3972690 : ℤ)) := ⟨join (by decide) b_9_9216.down b_9_9728.down (by decide)⟩
def b_11_8192 : PLift (tree 11 8192 = (8755419 : ℤ)) := ⟨join (by decide) b_10_8192.down b_10_9216.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10240 : PLift (tree 6 10240 = (207394 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10304 : PLift (tree 6 10304 = (193820 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10240 : PLift (tree 7 10240 = (401214 : ℤ)) := ⟨join (by decide) b_6_10240.down b_6_10304.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10368 : PLift (tree 6 10368 = (210562 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10432 : PLift (tree 6 10432 = (189694 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10368 : PLift (tree 7 10368 = (400256 : ℤ)) := ⟨join (by decide) b_6_10368.down b_6_10432.down (by decide)⟩
private def b_8_10240 : PLift (tree 8 10240 = (801470 : ℤ)) := ⟨join (by decide) b_7_10240.down b_7_10368.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10496 : PLift (tree 6 10496 = (172195 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10560 : PLift (tree 6 10560 = (207728 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10496 : PLift (tree 7 10496 = (379923 : ℤ)) := ⟨join (by decide) b_6_10496.down b_6_10560.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10624 : PLift (tree 6 10624 = (200089 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10688 : PLift (tree 6 10688 = (238119 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10624 : PLift (tree 7 10624 = (438208 : ℤ)) := ⟨join (by decide) b_6_10624.down b_6_10688.down (by decide)⟩
private def b_8_10496 : PLift (tree 8 10496 = (818131 : ℤ)) := ⟨join (by decide) b_7_10496.down b_7_10624.down (by decide)⟩
private def b_9_10240 : PLift (tree 9 10240 = (1619601 : ℤ)) := ⟨join (by decide) b_8_10240.down b_8_10496.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10752 : PLift (tree 6 10752 = (187591 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10816 : PLift (tree 6 10816 = (152492 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10752 : PLift (tree 7 10752 = (340083 : ℤ)) := ⟨join (by decide) b_6_10752.down b_6_10816.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10880 : PLift (tree 6 10880 = (218797 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_10944 : PLift (tree 6 10944 = (194036 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_10880 : PLift (tree 7 10880 = (412833 : ℤ)) := ⟨join (by decide) b_6_10880.down b_6_10944.down (by decide)⟩
private def b_8_10752 : PLift (tree 8 10752 = (752916 : ℤ)) := ⟨join (by decide) b_7_10752.down b_7_10880.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11008 : PLift (tree 6 11008 = (206021 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11072 : PLift (tree 6 11072 = (176935 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11008 : PLift (tree 7 11008 = (382956 : ℤ)) := ⟨join (by decide) b_6_11008.down b_6_11072.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11136 : PLift (tree 6 11136 = (214687 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11200 : PLift (tree 6 11200 = (168961 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11136 : PLift (tree 7 11136 = (383648 : ℤ)) := ⟨join (by decide) b_6_11136.down b_6_11200.down (by decide)⟩
private def b_8_11008 : PLift (tree 8 11008 = (766604 : ℤ)) := ⟨join (by decide) b_7_11008.down b_7_11136.down (by decide)⟩
private def b_9_10752 : PLift (tree 9 10752 = (1519520 : ℤ)) := ⟨join (by decide) b_8_10752.down b_8_11008.down (by decide)⟩
private def b_10_10240 : PLift (tree 10 10240 = (3139121 : ℤ)) := ⟨join (by decide) b_9_10240.down b_9_10752.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11264 : PLift (tree 6 11264 = (206220 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11328 : PLift (tree 6 11328 = (211846 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11264 : PLift (tree 7 11264 = (418066 : ℤ)) := ⟨join (by decide) b_6_11264.down b_6_11328.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11392 : PLift (tree 6 11392 = (179276 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11456 : PLift (tree 6 11456 = (191514 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11392 : PLift (tree 7 11392 = (370790 : ℤ)) := ⟨join (by decide) b_6_11392.down b_6_11456.down (by decide)⟩
private def b_8_11264 : PLift (tree 8 11264 = (788856 : ℤ)) := ⟨join (by decide) b_7_11264.down b_7_11392.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11520 : PLift (tree 6 11520 = (124254 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11584 : PLift (tree 6 11584 = (220791 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11520 : PLift (tree 7 11520 = (345045 : ℤ)) := ⟨join (by decide) b_6_11520.down b_6_11584.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11648 : PLift (tree 6 11648 = (127021 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11712 : PLift (tree 6 11712 = (184481 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11648 : PLift (tree 7 11648 = (311502 : ℤ)) := ⟨join (by decide) b_6_11648.down b_6_11712.down (by decide)⟩
private def b_8_11520 : PLift (tree 8 11520 = (656547 : ℤ)) := ⟨join (by decide) b_7_11520.down b_7_11648.down (by decide)⟩
private def b_9_11264 : PLift (tree 9 11264 = (1445403 : ℤ)) := ⟨join (by decide) b_8_11264.down b_8_11520.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11776 : PLift (tree 6 11776 = (154924 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11840 : PLift (tree 6 11840 = (163404 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11776 : PLift (tree 7 11776 = (318328 : ℤ)) := ⟨join (by decide) b_6_11776.down b_6_11840.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11904 : PLift (tree 6 11904 = (151292 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_11968 : PLift (tree 6 11968 = (164877 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_11904 : PLift (tree 7 11904 = (316169 : ℤ)) := ⟨join (by decide) b_6_11904.down b_6_11968.down (by decide)⟩
private def b_8_11776 : PLift (tree 8 11776 = (634497 : ℤ)) := ⟨join (by decide) b_7_11776.down b_7_11904.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12032 : PLift (tree 6 12032 = (181234 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12096 : PLift (tree 6 12096 = (174302 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12032 : PLift (tree 7 12032 = (355536 : ℤ)) := ⟨join (by decide) b_6_12032.down b_6_12096.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12160 : PLift (tree 6 12160 = (128979 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12224 : PLift (tree 6 12224 = (128093 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12160 : PLift (tree 7 12160 = (257072 : ℤ)) := ⟨join (by decide) b_6_12160.down b_6_12224.down (by decide)⟩
private def b_8_12032 : PLift (tree 8 12032 = (612608 : ℤ)) := ⟨join (by decide) b_7_12032.down b_7_12160.down (by decide)⟩
private def b_9_11776 : PLift (tree 9 11776 = (1247105 : ℤ)) := ⟨join (by decide) b_8_11776.down b_8_12032.down (by decide)⟩
private def b_10_11264 : PLift (tree 10 11264 = (2692508 : ℤ)) := ⟨join (by decide) b_9_11264.down b_9_11776.down (by decide)⟩
def b_11_10240 : PLift (tree 11 10240 = (5831629 : ℤ)) := ⟨join (by decide) b_10_10240.down b_10_11264.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12288 : PLift (tree 6 12288 = (148066 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12352 : PLift (tree 6 12352 = (161092 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12288 : PLift (tree 7 12288 = (309158 : ℤ)) := ⟨join (by decide) b_6_12288.down b_6_12352.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12416 : PLift (tree 6 12416 = (190796 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12480 : PLift (tree 6 12480 = (169713 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12416 : PLift (tree 7 12416 = (360509 : ℤ)) := ⟨join (by decide) b_6_12416.down b_6_12480.down (by decide)⟩
private def b_8_12288 : PLift (tree 8 12288 = (669667 : ℤ)) := ⟨join (by decide) b_7_12288.down b_7_12416.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12544 : PLift (tree 6 12544 = (159562 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12608 : PLift (tree 6 12608 = (122568 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12544 : PLift (tree 7 12544 = (282130 : ℤ)) := ⟨join (by decide) b_6_12544.down b_6_12608.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12672 : PLift (tree 6 12672 = (166323 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12736 : PLift (tree 6 12736 = (130322 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12672 : PLift (tree 7 12672 = (296645 : ℤ)) := ⟨join (by decide) b_6_12672.down b_6_12736.down (by decide)⟩
private def b_8_12544 : PLift (tree 8 12544 = (578775 : ℤ)) := ⟨join (by decide) b_7_12544.down b_7_12672.down (by decide)⟩
private def b_9_12288 : PLift (tree 9 12288 = (1248442 : ℤ)) := ⟨join (by decide) b_8_12288.down b_8_12544.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12800 : PLift (tree 6 12800 = (124766 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12864 : PLift (tree 6 12864 = (128593 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12800 : PLift (tree 7 12800 = (253359 : ℤ)) := ⟨join (by decide) b_6_12800.down b_6_12864.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12928 : PLift (tree 6 12928 = (140654 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_12992 : PLift (tree 6 12992 = (147807 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_12928 : PLift (tree 7 12928 = (288461 : ℤ)) := ⟨join (by decide) b_6_12928.down b_6_12992.down (by decide)⟩
private def b_8_12800 : PLift (tree 8 12800 = (541820 : ℤ)) := ⟨join (by decide) b_7_12800.down b_7_12928.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13056 : PLift (tree 6 13056 = (111205 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13120 : PLift (tree 6 13120 = (134289 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13056 : PLift (tree 7 13056 = (245494 : ℤ)) := ⟨join (by decide) b_6_13056.down b_6_13120.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13184 : PLift (tree 6 13184 = (142063 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13248 : PLift (tree 6 13248 = (102406 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13184 : PLift (tree 7 13184 = (244469 : ℤ)) := ⟨join (by decide) b_6_13184.down b_6_13248.down (by decide)⟩
private def b_8_13056 : PLift (tree 8 13056 = (489963 : ℤ)) := ⟨join (by decide) b_7_13056.down b_7_13184.down (by decide)⟩
private def b_9_12800 : PLift (tree 9 12800 = (1031783 : ℤ)) := ⟨join (by decide) b_8_12800.down b_8_13056.down (by decide)⟩
private def b_10_12288 : PLift (tree 10 12288 = (2280225 : ℤ)) := ⟨join (by decide) b_9_12288.down b_9_12800.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13312 : PLift (tree 6 13312 = (150935 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13376 : PLift (tree 6 13376 = (117503 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13312 : PLift (tree 7 13312 = (268438 : ℤ)) := ⟨join (by decide) b_6_13312.down b_6_13376.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13440 : PLift (tree 6 13440 = (91749 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13504 : PLift (tree 6 13504 = (110703 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13440 : PLift (tree 7 13440 = (202452 : ℤ)) := ⟨join (by decide) b_6_13440.down b_6_13504.down (by decide)⟩
private def b_8_13312 : PLift (tree 8 13312 = (470890 : ℤ)) := ⟨join (by decide) b_7_13312.down b_7_13440.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13568 : PLift (tree 6 13568 = (159970 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13632 : PLift (tree 6 13632 = (98259 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13568 : PLift (tree 7 13568 = (258229 : ℤ)) := ⟨join (by decide) b_6_13568.down b_6_13632.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13696 : PLift (tree 6 13696 = (116640 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13760 : PLift (tree 6 13760 = (120868 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13696 : PLift (tree 7 13696 = (237508 : ℤ)) := ⟨join (by decide) b_6_13696.down b_6_13760.down (by decide)⟩
private def b_8_13568 : PLift (tree 8 13568 = (495737 : ℤ)) := ⟨join (by decide) b_7_13568.down b_7_13696.down (by decide)⟩
private def b_9_13312 : PLift (tree 9 13312 = (966627 : ℤ)) := ⟨join (by decide) b_8_13312.down b_8_13568.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13824 : PLift (tree 6 13824 = (109594 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13888 : PLift (tree 6 13888 = (110221 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13824 : PLift (tree 7 13824 = (219815 : ℤ)) := ⟨join (by decide) b_6_13824.down b_6_13888.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_13952 : PLift (tree 6 13952 = (118585 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14016 : PLift (tree 6 14016 = (99055 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_13952 : PLift (tree 7 13952 = (217640 : ℤ)) := ⟨join (by decide) b_6_13952.down b_6_14016.down (by decide)⟩
private def b_8_13824 : PLift (tree 8 13824 = (437455 : ℤ)) := ⟨join (by decide) b_7_13824.down b_7_13952.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14080 : PLift (tree 6 14080 = (167645 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14144 : PLift (tree 6 14144 = (134333 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14080 : PLift (tree 7 14080 = (301978 : ℤ)) := ⟨join (by decide) b_6_14080.down b_6_14144.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14208 : PLift (tree 6 14208 = (87969 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14272 : PLift (tree 6 14272 = (135351 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14208 : PLift (tree 7 14208 = (223320 : ℤ)) := ⟨join (by decide) b_6_14208.down b_6_14272.down (by decide)⟩
private def b_8_14080 : PLift (tree 8 14080 = (525298 : ℤ)) := ⟨join (by decide) b_7_14080.down b_7_14208.down (by decide)⟩
private def b_9_13824 : PLift (tree 9 13824 = (962753 : ℤ)) := ⟨join (by decide) b_8_13824.down b_8_14080.down (by decide)⟩
private def b_10_13312 : PLift (tree 10 13312 = (1929380 : ℤ)) := ⟨join (by decide) b_9_13312.down b_9_13824.down (by decide)⟩
def b_11_12288 : PLift (tree 11 12288 = (4209605 : ℤ)) := ⟨join (by decide) b_10_12288.down b_10_13312.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14336 : PLift (tree 6 14336 = (159730 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14400 : PLift (tree 6 14400 = (140177 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14336 : PLift (tree 7 14336 = (299907 : ℤ)) := ⟨join (by decide) b_6_14336.down b_6_14400.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14464 : PLift (tree 6 14464 = (100218 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14528 : PLift (tree 6 14528 = (127356 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14464 : PLift (tree 7 14464 = (227574 : ℤ)) := ⟨join (by decide) b_6_14464.down b_6_14528.down (by decide)⟩
private def b_8_14336 : PLift (tree 8 14336 = (527481 : ℤ)) := ⟨join (by decide) b_7_14336.down b_7_14464.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14592 : PLift (tree 6 14592 = (107661 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14656 : PLift (tree 6 14656 = (125487 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14592 : PLift (tree 7 14592 = (233148 : ℤ)) := ⟨join (by decide) b_6_14592.down b_6_14656.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14720 : PLift (tree 6 14720 = (81750 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14784 : PLift (tree 6 14784 = (108975 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14720 : PLift (tree 7 14720 = (190725 : ℤ)) := ⟨join (by decide) b_6_14720.down b_6_14784.down (by decide)⟩
private def b_8_14592 : PLift (tree 8 14592 = (423873 : ℤ)) := ⟨join (by decide) b_7_14592.down b_7_14720.down (by decide)⟩
private def b_9_14336 : PLift (tree 9 14336 = (951354 : ℤ)) := ⟨join (by decide) b_8_14336.down b_8_14592.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14848 : PLift (tree 6 14848 = (128308 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14912 : PLift (tree 6 14912 = (66076 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14848 : PLift (tree 7 14848 = (194384 : ℤ)) := ⟨join (by decide) b_6_14848.down b_6_14912.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_14976 : PLift (tree 6 14976 = (125713 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15040 : PLift (tree 6 15040 = (95395 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_14976 : PLift (tree 7 14976 = (221108 : ℤ)) := ⟨join (by decide) b_6_14976.down b_6_15040.down (by decide)⟩
private def b_8_14848 : PLift (tree 8 14848 = (415492 : ℤ)) := ⟨join (by decide) b_7_14848.down b_7_14976.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15104 : PLift (tree 6 15104 = (95274 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15168 : PLift (tree 6 15168 = (82203 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15104 : PLift (tree 7 15104 = (177477 : ℤ)) := ⟨join (by decide) b_6_15104.down b_6_15168.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15232 : PLift (tree 6 15232 = (105364 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15296 : PLift (tree 6 15296 = (97785 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15232 : PLift (tree 7 15232 = (203149 : ℤ)) := ⟨join (by decide) b_6_15232.down b_6_15296.down (by decide)⟩
private def b_8_15104 : PLift (tree 8 15104 = (380626 : ℤ)) := ⟨join (by decide) b_7_15104.down b_7_15232.down (by decide)⟩
private def b_9_14848 : PLift (tree 9 14848 = (796118 : ℤ)) := ⟨join (by decide) b_8_14848.down b_8_15104.down (by decide)⟩
private def b_10_14336 : PLift (tree 10 14336 = (1747472 : ℤ)) := ⟨join (by decide) b_9_14336.down b_9_14848.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15360 : PLift (tree 6 15360 = (93798 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15424 : PLift (tree 6 15424 = (87044 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15360 : PLift (tree 7 15360 = (180842 : ℤ)) := ⟨join (by decide) b_6_15360.down b_6_15424.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15488 : PLift (tree 6 15488 = (69805 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15552 : PLift (tree 6 15552 = (95071 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15488 : PLift (tree 7 15488 = (164876 : ℤ)) := ⟨join (by decide) b_6_15488.down b_6_15552.down (by decide)⟩
private def b_8_15360 : PLift (tree 8 15360 = (345718 : ℤ)) := ⟨join (by decide) b_7_15360.down b_7_15488.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15616 : PLift (tree 6 15616 = (83622 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15680 : PLift (tree 6 15680 = (86095 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15616 : PLift (tree 7 15616 = (169717 : ℤ)) := ⟨join (by decide) b_6_15616.down b_6_15680.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15744 : PLift (tree 6 15744 = (111414 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15808 : PLift (tree 6 15808 = (115326 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15744 : PLift (tree 7 15744 = (226740 : ℤ)) := ⟨join (by decide) b_6_15744.down b_6_15808.down (by decide)⟩
private def b_8_15616 : PLift (tree 8 15616 = (396457 : ℤ)) := ⟨join (by decide) b_7_15616.down b_7_15744.down (by decide)⟩
private def b_9_15360 : PLift (tree 9 15360 = (742175 : ℤ)) := ⟨join (by decide) b_8_15360.down b_8_15616.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15872 : PLift (tree 6 15872 = (81577 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_15936 : PLift (tree 6 15936 = (104456 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_15872 : PLift (tree 7 15872 = (186033 : ℤ)) := ⟨join (by decide) b_6_15872.down b_6_15936.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16000 : PLift (tree 6 16000 = (94688 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16064 : PLift (tree 6 16064 = (53452 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16000 : PLift (tree 7 16000 = (148140 : ℤ)) := ⟨join (by decide) b_6_16000.down b_6_16064.down (by decide)⟩
private def b_8_15872 : PLift (tree 8 15872 = (334173 : ℤ)) := ⟨join (by decide) b_7_15872.down b_7_16000.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16128 : PLift (tree 6 16128 = (111353 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16192 : PLift (tree 6 16192 = (80665 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16128 : PLift (tree 7 16128 = (192018 : ℤ)) := ⟨join (by decide) b_6_16128.down b_6_16192.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16256 : PLift (tree 6 16256 = (91183 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16320 : PLift (tree 6 16320 = (105433 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16256 : PLift (tree 7 16256 = (196616 : ℤ)) := ⟨join (by decide) b_6_16256.down b_6_16320.down (by decide)⟩
private def b_8_16128 : PLift (tree 8 16128 = (388634 : ℤ)) := ⟨join (by decide) b_7_16128.down b_7_16256.down (by decide)⟩
private def b_9_15872 : PLift (tree 9 15872 = (722807 : ℤ)) := ⟨join (by decide) b_8_15872.down b_8_16128.down (by decide)⟩
private def b_10_15360 : PLift (tree 10 15360 = (1464982 : ℤ)) := ⟨join (by decide) b_9_15360.down b_9_15872.down (by decide)⟩
def b_11_14336 : PLift (tree 11 14336 = (3212454 : ℤ)) := ⟨join (by decide) b_10_14336.down b_10_15360.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16384 : PLift (tree 6 16384 = (62531 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16448 : PLift (tree 6 16448 = (82648 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16384 : PLift (tree 7 16384 = (145179 : ℤ)) := ⟨join (by decide) b_6_16384.down b_6_16448.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16512 : PLift (tree 6 16512 = (104944 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16576 : PLift (tree 6 16576 = (99431 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16512 : PLift (tree 7 16512 = (204375 : ℤ)) := ⟨join (by decide) b_6_16512.down b_6_16576.down (by decide)⟩
private def b_8_16384 : PLift (tree 8 16384 = (349554 : ℤ)) := ⟨join (by decide) b_7_16384.down b_7_16512.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16640 : PLift (tree 6 16640 = (70275 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16704 : PLift (tree 6 16704 = (87054 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16640 : PLift (tree 7 16640 = (157329 : ℤ)) := ⟨join (by decide) b_6_16640.down b_6_16704.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16768 : PLift (tree 6 16768 = (60185 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16832 : PLift (tree 6 16832 = (79697 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16768 : PLift (tree 7 16768 = (139882 : ℤ)) := ⟨join (by decide) b_6_16768.down b_6_16832.down (by decide)⟩
private def b_8_16640 : PLift (tree 8 16640 = (297211 : ℤ)) := ⟨join (by decide) b_7_16640.down b_7_16768.down (by decide)⟩
private def b_9_16384 : PLift (tree 9 16384 = (646765 : ℤ)) := ⟨join (by decide) b_8_16384.down b_8_16640.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16896 : PLift (tree 6 16896 = (76884 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_16960 : PLift (tree 6 16960 = (88493 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_16896 : PLift (tree 7 16896 = (165377 : ℤ)) := ⟨join (by decide) b_6_16896.down b_6_16960.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17024 : PLift (tree 6 17024 = (104711 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17088 : PLift (tree 6 17088 = (110906 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17024 : PLift (tree 7 17024 = (215617 : ℤ)) := ⟨join (by decide) b_6_17024.down b_6_17088.down (by decide)⟩
private def b_8_16896 : PLift (tree 8 16896 = (380994 : ℤ)) := ⟨join (by decide) b_7_16896.down b_7_17024.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17152 : PLift (tree 6 17152 = (85288 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17216 : PLift (tree 6 17216 = (69239 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17152 : PLift (tree 7 17152 = (154527 : ℤ)) := ⟨join (by decide) b_6_17152.down b_6_17216.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17280 : PLift (tree 6 17280 = (62277 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17344 : PLift (tree 6 17344 = (55789 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17280 : PLift (tree 7 17280 = (118066 : ℤ)) := ⟨join (by decide) b_6_17280.down b_6_17344.down (by decide)⟩
private def b_8_17152 : PLift (tree 8 17152 = (272593 : ℤ)) := ⟨join (by decide) b_7_17152.down b_7_17280.down (by decide)⟩
private def b_9_16896 : PLift (tree 9 16896 = (653587 : ℤ)) := ⟨join (by decide) b_8_16896.down b_8_17152.down (by decide)⟩
private def b_10_16384 : PLift (tree 10 16384 = (1300352 : ℤ)) := ⟨join (by decide) b_9_16384.down b_9_16896.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17408 : PLift (tree 6 17408 = (83274 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17472 : PLift (tree 6 17472 = (66700 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17408 : PLift (tree 7 17408 = (149974 : ℤ)) := ⟨join (by decide) b_6_17408.down b_6_17472.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17536 : PLift (tree 6 17536 = (53238 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17600 : PLift (tree 6 17600 = (94154 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17536 : PLift (tree 7 17536 = (147392 : ℤ)) := ⟨join (by decide) b_6_17536.down b_6_17600.down (by decide)⟩
private def b_8_17408 : PLift (tree 8 17408 = (297366 : ℤ)) := ⟨join (by decide) b_7_17408.down b_7_17536.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17664 : PLift (tree 6 17664 = (78665 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17728 : PLift (tree 6 17728 = (43369 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17664 : PLift (tree 7 17664 = (122034 : ℤ)) := ⟨join (by decide) b_6_17664.down b_6_17728.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17792 : PLift (tree 6 17792 = (79694 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17856 : PLift (tree 6 17856 = (79892 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17792 : PLift (tree 7 17792 = (159586 : ℤ)) := ⟨join (by decide) b_6_17792.down b_6_17856.down (by decide)⟩
private def b_8_17664 : PLift (tree 8 17664 = (281620 : ℤ)) := ⟨join (by decide) b_7_17664.down b_7_17792.down (by decide)⟩
private def b_9_17408 : PLift (tree 9 17408 = (578986 : ℤ)) := ⟨join (by decide) b_8_17408.down b_8_17664.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17920 : PLift (tree 6 17920 = (86543 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_17984 : PLift (tree 6 17984 = (75947 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_17920 : PLift (tree 7 17920 = (162490 : ℤ)) := ⟨join (by decide) b_6_17920.down b_6_17984.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18048 : PLift (tree 6 18048 = (83394 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18112 : PLift (tree 6 18112 = (74907 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18048 : PLift (tree 7 18048 = (158301 : ℤ)) := ⟨join (by decide) b_6_18048.down b_6_18112.down (by decide)⟩
private def b_8_17920 : PLift (tree 8 17920 = (320791 : ℤ)) := ⟨join (by decide) b_7_17920.down b_7_18048.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18176 : PLift (tree 6 18176 = (75665 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18240 : PLift (tree 6 18240 = (102086 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18176 : PLift (tree 7 18176 = (177751 : ℤ)) := ⟨join (by decide) b_6_18176.down b_6_18240.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18304 : PLift (tree 6 18304 = (60266 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18368 : PLift (tree 6 18368 = (72065 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18304 : PLift (tree 7 18304 = (132331 : ℤ)) := ⟨join (by decide) b_6_18304.down b_6_18368.down (by decide)⟩
private def b_8_18176 : PLift (tree 8 18176 = (310082 : ℤ)) := ⟨join (by decide) b_7_18176.down b_7_18304.down (by decide)⟩
private def b_9_17920 : PLift (tree 9 17920 = (630873 : ℤ)) := ⟨join (by decide) b_8_17920.down b_8_18176.down (by decide)⟩
private def b_10_17408 : PLift (tree 10 17408 = (1209859 : ℤ)) := ⟨join (by decide) b_9_17408.down b_9_17920.down (by decide)⟩
def b_11_16384 : PLift (tree 11 16384 = (2510211 : ℤ)) := ⟨join (by decide) b_10_16384.down b_10_17408.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18432 : PLift (tree 6 18432 = (55086 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18496 : PLift (tree 6 18496 = (51318 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18432 : PLift (tree 7 18432 = (106404 : ℤ)) := ⟨join (by decide) b_6_18432.down b_6_18496.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18560 : PLift (tree 6 18560 = (66120 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18624 : PLift (tree 6 18624 = (82043 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18560 : PLift (tree 7 18560 = (148163 : ℤ)) := ⟨join (by decide) b_6_18560.down b_6_18624.down (by decide)⟩
private def b_8_18432 : PLift (tree 8 18432 = (254567 : ℤ)) := ⟨join (by decide) b_7_18432.down b_7_18560.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18688 : PLift (tree 6 18688 = (47326 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18752 : PLift (tree 6 18752 = (79317 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18688 : PLift (tree 7 18688 = (126643 : ℤ)) := ⟨join (by decide) b_6_18688.down b_6_18752.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18816 : PLift (tree 6 18816 = (95846 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18880 : PLift (tree 6 18880 = (79072 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18816 : PLift (tree 7 18816 = (174918 : ℤ)) := ⟨join (by decide) b_6_18816.down b_6_18880.down (by decide)⟩
private def b_8_18688 : PLift (tree 8 18688 = (301561 : ℤ)) := ⟨join (by decide) b_7_18688.down b_7_18816.down (by decide)⟩
private def b_9_18432 : PLift (tree 9 18432 = (556128 : ℤ)) := ⟨join (by decide) b_8_18432.down b_8_18688.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_18944 : PLift (tree 6 18944 = (40166 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19008 : PLift (tree 6 19008 = (40831 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_18944 : PLift (tree 7 18944 = (80997 : ℤ)) := ⟨join (by decide) b_6_18944.down b_6_19008.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19072 : PLift (tree 6 19072 = (49320 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19136 : PLift (tree 6 19136 = (65811 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19072 : PLift (tree 7 19072 = (115131 : ℤ)) := ⟨join (by decide) b_6_19072.down b_6_19136.down (by decide)⟩
private def b_8_18944 : PLift (tree 8 18944 = (196128 : ℤ)) := ⟨join (by decide) b_7_18944.down b_7_19072.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19200 : PLift (tree 6 19200 = (59043 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19264 : PLift (tree 6 19264 = (54820 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19200 : PLift (tree 7 19200 = (113863 : ℤ)) := ⟨join (by decide) b_6_19200.down b_6_19264.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19328 : PLift (tree 6 19328 = (63647 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19392 : PLift (tree 6 19392 = (86970 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19328 : PLift (tree 7 19328 = (150617 : ℤ)) := ⟨join (by decide) b_6_19328.down b_6_19392.down (by decide)⟩
private def b_8_19200 : PLift (tree 8 19200 = (264480 : ℤ)) := ⟨join (by decide) b_7_19200.down b_7_19328.down (by decide)⟩
private def b_9_18944 : PLift (tree 9 18944 = (460608 : ℤ)) := ⟨join (by decide) b_8_18944.down b_8_19200.down (by decide)⟩
private def b_10_18432 : PLift (tree 10 18432 = (1016736 : ℤ)) := ⟨join (by decide) b_9_18432.down b_9_18944.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19456 : PLift (tree 6 19456 = (77797 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19520 : PLift (tree 6 19520 = (50093 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19456 : PLift (tree 7 19456 = (127890 : ℤ)) := ⟨join (by decide) b_6_19456.down b_6_19520.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19584 : PLift (tree 6 19584 = (46983 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19648 : PLift (tree 6 19648 = (23280 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19584 : PLift (tree 7 19584 = (70263 : ℤ)) := ⟨join (by decide) b_6_19584.down b_6_19648.down (by decide)⟩
private def b_8_19456 : PLift (tree 8 19456 = (198153 : ℤ)) := ⟨join (by decide) b_7_19456.down b_7_19584.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19712 : PLift (tree 6 19712 = (69613 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19776 : PLift (tree 6 19776 = (46872 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19712 : PLift (tree 7 19712 = (116485 : ℤ)) := ⟨join (by decide) b_6_19712.down b_6_19776.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19840 : PLift (tree 6 19840 = (66205 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19904 : PLift (tree 6 19904 = (59886 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19840 : PLift (tree 7 19840 = (126091 : ℤ)) := ⟨join (by decide) b_6_19840.down b_6_19904.down (by decide)⟩
private def b_8_19712 : PLift (tree 8 19712 = (242576 : ℤ)) := ⟨join (by decide) b_7_19712.down b_7_19840.down (by decide)⟩
private def b_9_19456 : PLift (tree 9 19456 = (440729 : ℤ)) := ⟨join (by decide) b_8_19456.down b_8_19712.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_19968 : PLift (tree 6 19968 = (77468 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20032 : PLift (tree 6 20032 = (55226 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_19968 : PLift (tree 7 19968 = (132694 : ℤ)) := ⟨join (by decide) b_6_19968.down b_6_20032.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20096 : PLift (tree 6 20096 = (59459 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20160 : PLift (tree 6 20160 = (74835 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20096 : PLift (tree 7 20096 = (134294 : ℤ)) := ⟨join (by decide) b_6_20096.down b_6_20160.down (by decide)⟩
private def b_8_19968 : PLift (tree 8 19968 = (266988 : ℤ)) := ⟨join (by decide) b_7_19968.down b_7_20096.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20224 : PLift (tree 6 20224 = (50492 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20288 : PLift (tree 6 20288 = (57209 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20224 : PLift (tree 7 20224 = (107701 : ℤ)) := ⟨join (by decide) b_6_20224.down b_6_20288.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20352 : PLift (tree 6 20352 = (104346 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20416 : PLift (tree 6 20416 = (76931 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20352 : PLift (tree 7 20352 = (181277 : ℤ)) := ⟨join (by decide) b_6_20352.down b_6_20416.down (by decide)⟩
private def b_8_20224 : PLift (tree 8 20224 = (288978 : ℤ)) := ⟨join (by decide) b_7_20224.down b_7_20352.down (by decide)⟩
private def b_9_19968 : PLift (tree 9 19968 = (555966 : ℤ)) := ⟨join (by decide) b_8_19968.down b_8_20224.down (by decide)⟩
private def b_10_19456 : PLift (tree 10 19456 = (996695 : ℤ)) := ⟨join (by decide) b_9_19456.down b_9_19968.down (by decide)⟩
def b_11_18432 : PLift (tree 11 18432 = (2013431 : ℤ)) := ⟨join (by decide) b_10_18432.down b_10_19456.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20480 : PLift (tree 6 20480 = (52391 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20544 : PLift (tree 6 20544 = (64014 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20480 : PLift (tree 7 20480 = (116405 : ℤ)) := ⟨join (by decide) b_6_20480.down b_6_20544.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20608 : PLift (tree 6 20608 = (53182 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20672 : PLift (tree 6 20672 = (28417 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20608 : PLift (tree 7 20608 = (81599 : ℤ)) := ⟨join (by decide) b_6_20608.down b_6_20672.down (by decide)⟩
private def b_8_20480 : PLift (tree 8 20480 = (198004 : ℤ)) := ⟨join (by decide) b_7_20480.down b_7_20608.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20736 : PLift (tree 6 20736 = (66268 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20800 : PLift (tree 6 20800 = (72514 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20736 : PLift (tree 7 20736 = (138782 : ℤ)) := ⟨join (by decide) b_6_20736.down b_6_20800.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20864 : PLift (tree 6 20864 = (32174 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20928 : PLift (tree 6 20928 = (77949 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20864 : PLift (tree 7 20864 = (110123 : ℤ)) := ⟨join (by decide) b_6_20864.down b_6_20928.down (by decide)⟩
private def b_8_20736 : PLift (tree 8 20736 = (248905 : ℤ)) := ⟨join (by decide) b_7_20736.down b_7_20864.down (by decide)⟩
private def b_9_20480 : PLift (tree 9 20480 = (446909 : ℤ)) := ⟨join (by decide) b_8_20480.down b_8_20736.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_20992 : PLift (tree 6 20992 = (47444 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21056 : PLift (tree 6 21056 = (49014 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_20992 : PLift (tree 7 20992 = (96458 : ℤ)) := ⟨join (by decide) b_6_20992.down b_6_21056.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21120 : PLift (tree 6 21120 = (44014 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21184 : PLift (tree 6 21184 = (73542 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21120 : PLift (tree 7 21120 = (117556 : ℤ)) := ⟨join (by decide) b_6_21120.down b_6_21184.down (by decide)⟩
private def b_8_20992 : PLift (tree 8 20992 = (214014 : ℤ)) := ⟨join (by decide) b_7_20992.down b_7_21120.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21248 : PLift (tree 6 21248 = (42361 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21312 : PLift (tree 6 21312 = (48686 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21248 : PLift (tree 7 21248 = (91047 : ℤ)) := ⟨join (by decide) b_6_21248.down b_6_21312.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21376 : PLift (tree 6 21376 = (48216 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21440 : PLift (tree 6 21440 = (38276 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21376 : PLift (tree 7 21376 = (86492 : ℤ)) := ⟨join (by decide) b_6_21376.down b_6_21440.down (by decide)⟩
private def b_8_21248 : PLift (tree 8 21248 = (177539 : ℤ)) := ⟨join (by decide) b_7_21248.down b_7_21376.down (by decide)⟩
private def b_9_20992 : PLift (tree 9 20992 = (391553 : ℤ)) := ⟨join (by decide) b_8_20992.down b_8_21248.down (by decide)⟩
private def b_10_20480 : PLift (tree 10 20480 = (838462 : ℤ)) := ⟨join (by decide) b_9_20480.down b_9_20992.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21504 : PLift (tree 6 21504 = (64343 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21568 : PLift (tree 6 21568 = (52145 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21504 : PLift (tree 7 21504 = (116488 : ℤ)) := ⟨join (by decide) b_6_21504.down b_6_21568.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21632 : PLift (tree 6 21632 = (55802 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21696 : PLift (tree 6 21696 = (65645 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21632 : PLift (tree 7 21632 = (121447 : ℤ)) := ⟨join (by decide) b_6_21632.down b_6_21696.down (by decide)⟩
private def b_8_21504 : PLift (tree 8 21504 = (237935 : ℤ)) := ⟨join (by decide) b_7_21504.down b_7_21632.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21760 : PLift (tree 6 21760 = (55992 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21824 : PLift (tree 6 21824 = (26045 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21760 : PLift (tree 7 21760 = (82037 : ℤ)) := ⟨join (by decide) b_6_21760.down b_6_21824.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21888 : PLift (tree 6 21888 = (22427 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_21952 : PLift (tree 6 21952 = (41029 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_21888 : PLift (tree 7 21888 = (63456 : ℤ)) := ⟨join (by decide) b_6_21888.down b_6_21952.down (by decide)⟩
private def b_8_21760 : PLift (tree 8 21760 = (145493 : ℤ)) := ⟨join (by decide) b_7_21760.down b_7_21888.down (by decide)⟩
private def b_9_21504 : PLift (tree 9 21504 = (383428 : ℤ)) := ⟨join (by decide) b_8_21504.down b_8_21760.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22016 : PLift (tree 6 22016 = (47445 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22080 : PLift (tree 6 22080 = (51585 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22016 : PLift (tree 7 22016 = (99030 : ℤ)) := ⟨join (by decide) b_6_22016.down b_6_22080.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22144 : PLift (tree 6 22144 = (48700 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22208 : PLift (tree 6 22208 = (41569 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22144 : PLift (tree 7 22144 = (90269 : ℤ)) := ⟨join (by decide) b_6_22144.down b_6_22208.down (by decide)⟩
private def b_8_22016 : PLift (tree 8 22016 = (189299 : ℤ)) := ⟨join (by decide) b_7_22016.down b_7_22144.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22272 : PLift (tree 6 22272 = (41975 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22336 : PLift (tree 6 22336 = (38667 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22272 : PLift (tree 7 22272 = (80642 : ℤ)) := ⟨join (by decide) b_6_22272.down b_6_22336.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22400 : PLift (tree 6 22400 = (29002 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22464 : PLift (tree 6 22464 = (51433 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22400 : PLift (tree 7 22400 = (80435 : ℤ)) := ⟨join (by decide) b_6_22400.down b_6_22464.down (by decide)⟩
private def b_8_22272 : PLift (tree 8 22272 = (161077 : ℤ)) := ⟨join (by decide) b_7_22272.down b_7_22400.down (by decide)⟩
private def b_9_22016 : PLift (tree 9 22016 = (350376 : ℤ)) := ⟨join (by decide) b_8_22016.down b_8_22272.down (by decide)⟩
private def b_10_21504 : PLift (tree 10 21504 = (733804 : ℤ)) := ⟨join (by decide) b_9_21504.down b_9_22016.down (by decide)⟩
def b_11_20480 : PLift (tree 11 20480 = (1572266 : ℤ)) := ⟨join (by decide) b_10_20480.down b_10_21504.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22528 : PLift (tree 6 22528 = (41575 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22592 : PLift (tree 6 22592 = (43548 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22528 : PLift (tree 7 22528 = (85123 : ℤ)) := ⟨join (by decide) b_6_22528.down b_6_22592.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22656 : PLift (tree 6 22656 = (55769 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22720 : PLift (tree 6 22720 = (45308 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22656 : PLift (tree 7 22656 = (101077 : ℤ)) := ⟨join (by decide) b_6_22656.down b_6_22720.down (by decide)⟩
private def b_8_22528 : PLift (tree 8 22528 = (186200 : ℤ)) := ⟨join (by decide) b_7_22528.down b_7_22656.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22784 : PLift (tree 6 22784 = (31114 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22848 : PLift (tree 6 22848 = (34716 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22784 : PLift (tree 7 22784 = (65830 : ℤ)) := ⟨join (by decide) b_6_22784.down b_6_22848.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22912 : PLift (tree 6 22912 = (53594 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_22976 : PLift (tree 6 22976 = (63892 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_22912 : PLift (tree 7 22912 = (117486 : ℤ)) := ⟨join (by decide) b_6_22912.down b_6_22976.down (by decide)⟩
private def b_8_22784 : PLift (tree 8 22784 = (183316 : ℤ)) := ⟨join (by decide) b_7_22784.down b_7_22912.down (by decide)⟩
private def b_9_22528 : PLift (tree 9 22528 = (369516 : ℤ)) := ⟨join (by decide) b_8_22528.down b_8_22784.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23040 : PLift (tree 6 23040 = (51611 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23104 : PLift (tree 6 23104 = (34147 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23040 : PLift (tree 7 23040 = (85758 : ℤ)) := ⟨join (by decide) b_6_23040.down b_6_23104.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23168 : PLift (tree 6 23168 = (44310 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23232 : PLift (tree 6 23232 = (24972 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23168 : PLift (tree 7 23168 = (69282 : ℤ)) := ⟨join (by decide) b_6_23168.down b_6_23232.down (by decide)⟩
private def b_8_23040 : PLift (tree 8 23040 = (155040 : ℤ)) := ⟨join (by decide) b_7_23040.down b_7_23168.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23296 : PLift (tree 6 23296 = (71983 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23360 : PLift (tree 6 23360 = (39357 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23296 : PLift (tree 7 23296 = (111340 : ℤ)) := ⟨join (by decide) b_6_23296.down b_6_23360.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23424 : PLift (tree 6 23424 = (32294 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23488 : PLift (tree 6 23488 = (42930 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23424 : PLift (tree 7 23424 = (75224 : ℤ)) := ⟨join (by decide) b_6_23424.down b_6_23488.down (by decide)⟩
private def b_8_23296 : PLift (tree 8 23296 = (186564 : ℤ)) := ⟨join (by decide) b_7_23296.down b_7_23424.down (by decide)⟩
private def b_9_23040 : PLift (tree 9 23040 = (341604 : ℤ)) := ⟨join (by decide) b_8_23040.down b_8_23296.down (by decide)⟩
private def b_10_22528 : PLift (tree 10 22528 = (711120 : ℤ)) := ⟨join (by decide) b_9_22528.down b_9_23040.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23552 : PLift (tree 6 23552 = (48938 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23616 : PLift (tree 6 23616 = (31321 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23552 : PLift (tree 7 23552 = (80259 : ℤ)) := ⟨join (by decide) b_6_23552.down b_6_23616.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23680 : PLift (tree 6 23680 = (31684 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23744 : PLift (tree 6 23744 = (46977 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23680 : PLift (tree 7 23680 = (78661 : ℤ)) := ⟨join (by decide) b_6_23680.down b_6_23744.down (by decide)⟩
private def b_8_23552 : PLift (tree 8 23552 = (158920 : ℤ)) := ⟨join (by decide) b_7_23552.down b_7_23680.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23808 : PLift (tree 6 23808 = (40153 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23872 : PLift (tree 6 23872 = (41768 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23808 : PLift (tree 7 23808 = (81921 : ℤ)) := ⟨join (by decide) b_6_23808.down b_6_23872.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_23936 : PLift (tree 6 23936 = (59805 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24000 : PLift (tree 6 24000 = (28349 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_23936 : PLift (tree 7 23936 = (88154 : ℤ)) := ⟨join (by decide) b_6_23936.down b_6_24000.down (by decide)⟩
private def b_8_23808 : PLift (tree 8 23808 = (170075 : ℤ)) := ⟨join (by decide) b_7_23808.down b_7_23936.down (by decide)⟩
private def b_9_23552 : PLift (tree 9 23552 = (328995 : ℤ)) := ⟨join (by decide) b_8_23552.down b_8_23808.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24064 : PLift (tree 6 24064 = (51240 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24128 : PLift (tree 6 24128 = (24024 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24064 : PLift (tree 7 24064 = (75264 : ℤ)) := ⟨join (by decide) b_6_24064.down b_6_24128.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24192 : PLift (tree 6 24192 = (12968 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24256 : PLift (tree 6 24256 = (43662 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24192 : PLift (tree 7 24192 = (56630 : ℤ)) := ⟨join (by decide) b_6_24192.down b_6_24256.down (by decide)⟩
private def b_8_24064 : PLift (tree 8 24064 = (131894 : ℤ)) := ⟨join (by decide) b_7_24064.down b_7_24192.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24320 : PLift (tree 6 24320 = (46515 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24384 : PLift (tree 6 24384 = (31841 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24320 : PLift (tree 7 24320 = (78356 : ℤ)) := ⟨join (by decide) b_6_24320.down b_6_24384.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24448 : PLift (tree 6 24448 = (23398 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24512 : PLift (tree 6 24512 = (38828 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24448 : PLift (tree 7 24448 = (62226 : ℤ)) := ⟨join (by decide) b_6_24448.down b_6_24512.down (by decide)⟩
private def b_8_24320 : PLift (tree 8 24320 = (140582 : ℤ)) := ⟨join (by decide) b_7_24320.down b_7_24448.down (by decide)⟩
private def b_9_24064 : PLift (tree 9 24064 = (272476 : ℤ)) := ⟨join (by decide) b_8_24064.down b_8_24320.down (by decide)⟩
private def b_10_23552 : PLift (tree 10 23552 = (601471 : ℤ)) := ⟨join (by decide) b_9_23552.down b_9_24064.down (by decide)⟩
def b_11_22528 : PLift (tree 11 22528 = (1312591 : ℤ)) := ⟨join (by decide) b_10_22528.down b_10_23552.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24576 : PLift (tree 6 24576 = (51949 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24640 : PLift (tree 6 24640 = (41120 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24576 : PLift (tree 7 24576 = (93069 : ℤ)) := ⟨join (by decide) b_6_24576.down b_6_24640.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24704 : PLift (tree 6 24704 = (54376 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24768 : PLift (tree 6 24768 = (61092 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24704 : PLift (tree 7 24704 = (115468 : ℤ)) := ⟨join (by decide) b_6_24704.down b_6_24768.down (by decide)⟩
private def b_8_24576 : PLift (tree 8 24576 = (208537 : ℤ)) := ⟨join (by decide) b_7_24576.down b_7_24704.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24832 : PLift (tree 6 24832 = (41408 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24896 : PLift (tree 6 24896 = (6123 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24832 : PLift (tree 7 24832 = (47531 : ℤ)) := ⟨join (by decide) b_6_24832.down b_6_24896.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_24960 : PLift (tree 6 24960 = (8929 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25024 : PLift (tree 6 25024 = (17077 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_24960 : PLift (tree 7 24960 = (26006 : ℤ)) := ⟨join (by decide) b_6_24960.down b_6_25024.down (by decide)⟩
private def b_8_24832 : PLift (tree 8 24832 = (73537 : ℤ)) := ⟨join (by decide) b_7_24832.down b_7_24960.down (by decide)⟩
private def b_9_24576 : PLift (tree 9 24576 = (282074 : ℤ)) := ⟨join (by decide) b_8_24576.down b_8_24832.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25088 : PLift (tree 6 25088 = (23250 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25152 : PLift (tree 6 25152 = (46715 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25088 : PLift (tree 7 25088 = (69965 : ℤ)) := ⟨join (by decide) b_6_25088.down b_6_25152.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25216 : PLift (tree 6 25216 = (20871 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25280 : PLift (tree 6 25280 = (28942 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25216 : PLift (tree 7 25216 = (49813 : ℤ)) := ⟨join (by decide) b_6_25216.down b_6_25280.down (by decide)⟩
private def b_8_25088 : PLift (tree 8 25088 = (119778 : ℤ)) := ⟨join (by decide) b_7_25088.down b_7_25216.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25344 : PLift (tree 6 25344 = (42541 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25408 : PLift (tree 6 25408 = (21045 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25344 : PLift (tree 7 25344 = (63586 : ℤ)) := ⟨join (by decide) b_6_25344.down b_6_25408.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25472 : PLift (tree 6 25472 = (35047 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25536 : PLift (tree 6 25536 = (36906 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25472 : PLift (tree 7 25472 = (71953 : ℤ)) := ⟨join (by decide) b_6_25472.down b_6_25536.down (by decide)⟩
private def b_8_25344 : PLift (tree 8 25344 = (135539 : ℤ)) := ⟨join (by decide) b_7_25344.down b_7_25472.down (by decide)⟩
private def b_9_25088 : PLift (tree 9 25088 = (255317 : ℤ)) := ⟨join (by decide) b_8_25088.down b_8_25344.down (by decide)⟩
private def b_10_24576 : PLift (tree 10 24576 = (537391 : ℤ)) := ⟨join (by decide) b_9_24576.down b_9_25088.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25600 : PLift (tree 6 25600 = (57259 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25664 : PLift (tree 6 25664 = (26344 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25600 : PLift (tree 7 25600 = (83603 : ℤ)) := ⟨join (by decide) b_6_25600.down b_6_25664.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25728 : PLift (tree 6 25728 = (40175 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25792 : PLift (tree 6 25792 = (34044 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25728 : PLift (tree 7 25728 = (74219 : ℤ)) := ⟨join (by decide) b_6_25728.down b_6_25792.down (by decide)⟩
private def b_8_25600 : PLift (tree 8 25600 = (157822 : ℤ)) := ⟨join (by decide) b_7_25600.down b_7_25728.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25856 : PLift (tree 6 25856 = (44158 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25920 : PLift (tree 6 25920 = (42550 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25856 : PLift (tree 7 25856 = (86708 : ℤ)) := ⟨join (by decide) b_6_25856.down b_6_25920.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_25984 : PLift (tree 6 25984 = (36625 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26048 : PLift (tree 6 26048 = (21450 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_25984 : PLift (tree 7 25984 = (58075 : ℤ)) := ⟨join (by decide) b_6_25984.down b_6_26048.down (by decide)⟩
private def b_8_25856 : PLift (tree 8 25856 = (144783 : ℤ)) := ⟨join (by decide) b_7_25856.down b_7_25984.down (by decide)⟩
private def b_9_25600 : PLift (tree 9 25600 = (302605 : ℤ)) := ⟨join (by decide) b_8_25600.down b_8_25856.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26112 : PLift (tree 6 26112 = (36101 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26176 : PLift (tree 6 26176 = (14538 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26112 : PLift (tree 7 26112 = (50639 : ℤ)) := ⟨join (by decide) b_6_26112.down b_6_26176.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26240 : PLift (tree 6 26240 = (40623 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26304 : PLift (tree 6 26304 = (28263 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26240 : PLift (tree 7 26240 = (68886 : ℤ)) := ⟨join (by decide) b_6_26240.down b_6_26304.down (by decide)⟩
private def b_8_26112 : PLift (tree 8 26112 = (119525 : ℤ)) := ⟨join (by decide) b_7_26112.down b_7_26240.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26368 : PLift (tree 6 26368 = (34434 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26432 : PLift (tree 6 26432 = (35791 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26368 : PLift (tree 7 26368 = (70225 : ℤ)) := ⟨join (by decide) b_6_26368.down b_6_26432.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26496 : PLift (tree 6 26496 = (43780 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26560 : PLift (tree 6 26560 = (38415 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26496 : PLift (tree 7 26496 = (82195 : ℤ)) := ⟨join (by decide) b_6_26496.down b_6_26560.down (by decide)⟩
private def b_8_26368 : PLift (tree 8 26368 = (152420 : ℤ)) := ⟨join (by decide) b_7_26368.down b_7_26496.down (by decide)⟩
private def b_9_26112 : PLift (tree 9 26112 = (271945 : ℤ)) := ⟨join (by decide) b_8_26112.down b_8_26368.down (by decide)⟩
private def b_10_25600 : PLift (tree 10 25600 = (574550 : ℤ)) := ⟨join (by decide) b_9_25600.down b_9_26112.down (by decide)⟩
def b_11_24576 : PLift (tree 11 24576 = (1111941 : ℤ)) := ⟨join (by decide) b_10_24576.down b_10_25600.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26624 : PLift (tree 6 26624 = (53871 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26688 : PLift (tree 6 26688 = (21325 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26624 : PLift (tree 7 26624 = (75196 : ℤ)) := ⟨join (by decide) b_6_26624.down b_6_26688.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26752 : PLift (tree 6 26752 = (40407 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26816 : PLift (tree 6 26816 = (34060 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26752 : PLift (tree 7 26752 = (74467 : ℤ)) := ⟨join (by decide) b_6_26752.down b_6_26816.down (by decide)⟩
private def b_8_26624 : PLift (tree 8 26624 = (149663 : ℤ)) := ⟨join (by decide) b_7_26624.down b_7_26752.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26880 : PLift (tree 6 26880 = (30784 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_26944 : PLift (tree 6 26944 = (32007 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_26880 : PLift (tree 7 26880 = (62791 : ℤ)) := ⟨join (by decide) b_6_26880.down b_6_26944.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27008 : PLift (tree 6 27008 = (29585 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27072 : PLift (tree 6 27072 = (32332 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27008 : PLift (tree 7 27008 = (61917 : ℤ)) := ⟨join (by decide) b_6_27008.down b_6_27072.down (by decide)⟩
private def b_8_26880 : PLift (tree 8 26880 = (124708 : ℤ)) := ⟨join (by decide) b_7_26880.down b_7_27008.down (by decide)⟩
private def b_9_26624 : PLift (tree 9 26624 = (274371 : ℤ)) := ⟨join (by decide) b_8_26624.down b_8_26880.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27136 : PLift (tree 6 27136 = (24389 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27200 : PLift (tree 6 27200 = (27192 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27136 : PLift (tree 7 27136 = (51581 : ℤ)) := ⟨join (by decide) b_6_27136.down b_6_27200.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27264 : PLift (tree 6 27264 = (26364 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27328 : PLift (tree 6 27328 = (44833 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27264 : PLift (tree 7 27264 = (71197 : ℤ)) := ⟨join (by decide) b_6_27264.down b_6_27328.down (by decide)⟩
private def b_8_27136 : PLift (tree 8 27136 = (122778 : ℤ)) := ⟨join (by decide) b_7_27136.down b_7_27264.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27392 : PLift (tree 6 27392 = (31675 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27456 : PLift (tree 6 27456 = (19406 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27392 : PLift (tree 7 27392 = (51081 : ℤ)) := ⟨join (by decide) b_6_27392.down b_6_27456.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27520 : PLift (tree 6 27520 = (34910 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27584 : PLift (tree 6 27584 = (19176 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27520 : PLift (tree 7 27520 = (54086 : ℤ)) := ⟨join (by decide) b_6_27520.down b_6_27584.down (by decide)⟩
private def b_8_27392 : PLift (tree 8 27392 = (105167 : ℤ)) := ⟨join (by decide) b_7_27392.down b_7_27520.down (by decide)⟩
private def b_9_27136 : PLift (tree 9 27136 = (227945 : ℤ)) := ⟨join (by decide) b_8_27136.down b_8_27392.down (by decide)⟩
private def b_10_26624 : PLift (tree 10 26624 = (502316 : ℤ)) := ⟨join (by decide) b_9_26624.down b_9_27136.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27648 : PLift (tree 6 27648 = (55712 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27712 : PLift (tree 6 27712 = (28274 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27648 : PLift (tree 7 27648 = (83986 : ℤ)) := ⟨join (by decide) b_6_27648.down b_6_27712.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27776 : PLift (tree 6 27776 = (41210 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27840 : PLift (tree 6 27840 = (45292 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27776 : PLift (tree 7 27776 = (86502 : ℤ)) := ⟨join (by decide) b_6_27776.down b_6_27840.down (by decide)⟩
private def b_8_27648 : PLift (tree 8 27648 = (170488 : ℤ)) := ⟨join (by decide) b_7_27648.down b_7_27776.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27904 : PLift (tree 6 27904 = (21422 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_27968 : PLift (tree 6 27968 = (22564 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_27904 : PLift (tree 7 27904 = (43986 : ℤ)) := ⟨join (by decide) b_6_27904.down b_6_27968.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28032 : PLift (tree 6 28032 = (41341 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28096 : PLift (tree 6 28096 = (44764 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_28032 : PLift (tree 7 28032 = (86105 : ℤ)) := ⟨join (by decide) b_6_28032.down b_6_28096.down (by decide)⟩
private def b_8_27904 : PLift (tree 8 27904 = (130091 : ℤ)) := ⟨join (by decide) b_7_27904.down b_7_28032.down (by decide)⟩
private def b_9_27648 : PLift (tree 9 27648 = (300579 : ℤ)) := ⟨join (by decide) b_8_27648.down b_8_27904.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28160 : PLift (tree 6 28160 = (24081 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28224 : PLift (tree 6 28224 = (30621 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_28160 : PLift (tree 7 28160 = (54702 : ℤ)) := ⟨join (by decide) b_6_28160.down b_6_28224.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28288 : PLift (tree 6 28288 = (19840 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28352 : PLift (tree 6 28352 = (9318 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_28288 : PLift (tree 7 28288 = (29158 : ℤ)) := ⟨join (by decide) b_6_28288.down b_6_28352.down (by decide)⟩
private def b_8_28160 : PLift (tree 8 28160 = (83860 : ℤ)) := ⟨join (by decide) b_7_28160.down b_7_28288.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28416 : PLift (tree 6 28416 = (52340 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28480 : PLift (tree 6 28480 = (29432 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_28416 : PLift (tree 7 28416 = (81772 : ℤ)) := ⟨join (by decide) b_6_28416.down b_6_28480.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28544 : PLift (tree 6 28544 = (40094 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28608 : PLift (tree 6 28608 = (29480 : ℤ)) := ⟨by decide +kernel⟩
private def b_7_28544 : PLift (tree 7 28544 = (69574 : ℤ)) := ⟨join (by decide) b_6_28544.down b_6_28608.down (by decide)⟩
private def b_8_28416 : PLift (tree 8 28416 = (151346 : ℤ)) := ⟨join (by decide) b_7_28416.down b_7_28544.down (by decide)⟩
private def b_9_28160 : PLift (tree 9 28160 = (235206 : ℤ)) := ⟨join (by decide) b_8_28160.down b_8_28416.down (by decide)⟩
private def b_10_27648 : PLift (tree 10 27648 = (535785 : ℤ)) := ⟨join (by decide) b_9_27648.down b_9_28160.down (by decide)⟩
def b_11_26624 : PLift (tree 11 26624 = (1038101 : ℤ)) := ⟨join (by decide) b_10_26624.down b_10_27648.down (by decide)⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_6_28672 : PLift (tree 6 28672 = (16499 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_2_28736 : PLift (tree 2 28736 = (0 : ℤ)) := ⟨by decide +kernel⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
private def b_0_28740 : PLift (tree 0 28740 = (0 : ℤ)) := ⟨by decide +kernel⟩
private def b_0_28741 : PLift (tree 0 28741 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_1_28740 : PLift (tree 1 28740 = (0 : ℤ)) := ⟨join (by decide) b_0_28740.down b_0_28741.down (by decide)⟩
private def b_1_28742 : PLift (tree 1 28742 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_2_28740 : PLift (tree 2 28740 = (0 : ℤ)) := ⟨join (by decide) b_1_28740.down b_1_28742.down (by decide)⟩
private def b_3_28736 : PLift (tree 3 28736 = (0 : ℤ)) := ⟨join (by decide) b_2_28736.down b_2_28740.down (by decide)⟩
private def b_3_28744 : PLift (tree 3 28744 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_4_28736 : PLift (tree 4 28736 = (0 : ℤ)) := ⟨join (by decide) b_3_28736.down b_3_28744.down (by decide)⟩
private def b_4_28752 : PLift (tree 4 28752 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_5_28736 : PLift (tree 5 28736 = (0 : ℤ)) := ⟨join (by decide) b_4_28736.down b_4_28752.down (by decide)⟩
private def b_5_28768 : PLift (tree 5 28768 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_6_28736 : PLift (tree 6 28736 = (0 : ℤ)) := ⟨join (by decide) b_5_28736.down b_5_28768.down (by decide)⟩
private def b_7_28672 : PLift (tree 7 28672 = (16499 : ℤ)) := ⟨join (by decide) b_6_28672.down b_6_28736.down (by decide)⟩
private def b_7_28800 : PLift (tree 7 28800 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_8_28672 : PLift (tree 8 28672 = (16499 : ℤ)) := ⟨join (by decide) b_7_28672.down b_7_28800.down (by decide)⟩
private def b_8_28928 : PLift (tree 8 28928 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_9_28672 : PLift (tree 9 28672 = (16499 : ℤ)) := ⟨join (by decide) b_8_28672.down b_8_28928.down (by decide)⟩
private def b_9_29184 : PLift (tree 9 29184 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_10_28672 : PLift (tree 10 28672 = (16499 : ℤ)) := ⟨join (by decide) b_9_28672.down b_9_29184.down (by decide)⟩
private def b_10_29696 : PLift (tree 10 29696 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
def b_11_28672 : PLift (tree 11 28672 = (16499 : ℤ)) := ⟨join (by decide) b_10_28672.down b_10_29696.down (by decide)⟩
def b_11_30720 : PLift (tree 11 30720 = (0 : ℤ)) := ⟨inactive _ _ (by decide)⟩
private def b_9_512 : PLift (tree 9 512 = (258897596 : ℤ)) := ⟨join (by decide) b_8_512.down b_8_768.down (by decide)⟩
private def b_12_4096 : PLift (tree 12 4096 = (42253836 : ℤ)) := ⟨join (by decide) b_11_4096.down b_11_6144.down (by decide)⟩
private def b_12_8192 : PLift (tree 12 8192 = (14587048 : ℤ)) := ⟨join (by decide) b_11_8192.down b_11_10240.down (by decide)⟩
private def b_12_12288 : PLift (tree 12 12288 = (7422059 : ℤ)) := ⟨join (by decide) b_11_12288.down b_11_14336.down (by decide)⟩
private def b_13_8192 : PLift (tree 13 8192 = (22009107 : ℤ)) := ⟨join (by decide) b_12_8192.down b_12_12288.down (by decide)⟩
private def b_12_16384 : PLift (tree 12 16384 = (4523642 : ℤ)) := ⟨join (by decide) b_11_16384.down b_11_18432.down (by decide)⟩
private def b_12_20480 : PLift (tree 12 20480 = (2884857 : ℤ)) := ⟨join (by decide) b_11_20480.down b_11_22528.down (by decide)⟩
private def b_13_16384 : PLift (tree 13 16384 = (7408499 : ℤ)) := ⟨join (by decide) b_12_16384.down b_12_20480.down (by decide)⟩
private def b_12_24576 : PLift (tree 12 24576 = (2150042 : ℤ)) := ⟨join (by decide) b_11_24576.down b_11_26624.down (by decide)⟩
private def b_12_28672 : PLift (tree 12 28672 = (16499 : ℤ)) := ⟨join (by decide) b_11_28672.down b_11_30720.down (by decide)⟩
private def b_13_24576 : PLift (tree 13 24576 = (2166541 : ℤ)) := ⟨join (by decide) b_12_24576.down b_12_28672.down (by decide)⟩
private def b_14_16384 : PLift (tree 14 16384 = (9575040 : ℤ)) := ⟨join (by decide) b_13_16384.down b_13_24576.down (by decide)⟩
end Astra247824.HardTail.Batch


namespace Astra247824.HardTail.Slice
private theorem cut_7_384 : rowPrefix 512 - rowPrefix 384 = (149323024 : ℤ) := (tree_interval 7 384).symm.trans Batch.b_7_384.down
private theorem cut_9_512 : rowPrefix 1024 - rowPrefix 512 = (258897596 : ℤ) := (tree_interval 9 512).symm.trans Batch.b_9_512.down
private theorem cut_10_1024 : rowPrefix 2048 - rowPrefix 1024 = (150449779 : ℤ) := (tree_interval 10 1024).symm.trans Batch.b_10_1024.down
private theorem cut_11_2048 : rowPrefix 4096 - rowPrefix 2048 = (80167434 : ℤ) := (tree_interval 11 2048).symm.trans Batch.b_11_2048.down
private theorem cut_12_4096 : rowPrefix 8192 - rowPrefix 4096 = (42253836 : ℤ) := (tree_interval 12 4096).symm.trans Batch.b_12_4096.down
private theorem cut_13_8192 : rowPrefix 16384 - rowPrefix 8192 = (22009107 : ℤ) := (tree_interval 13 8192).symm.trans Batch.b_13_8192.down
private theorem cut_14_16384 : rowPrefix 32768 - rowPrefix 16384 = (9575040 : ℤ) := (tree_interval 14 16384).symm.trans Batch.b_14_16384.down
theorem verified_slice_4 : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1.H4 := by
  change sourceTotal - sourcePrefix 384 = 712675816
  rw [total_original,full_eq,prefix_original,prefix_eq]
  exact (join_intervals (join_intervals (join_intervals (join_intervals (join_intervals (join_intervals cut_7_384 cut_9_512) cut_10_1024) cut_11_2048) cut_12_4096) cut_13_8192) cut_14_16384)
end Astra247824.HardTail.Slice
theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1.H4 := Astra247824.HardTail.Slice.verified_slice_4
