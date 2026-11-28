import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1

-- Reduction OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H3.R1.H3.R1 of step OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H3.R1.H3
-- Credit: @ehsanmok

/-!
# Columns 18 and 19 for the exponent class q = 41 mod 105 of A249609

Here a = 3240*q+2705 with q mod 105 = 41, so a mod 340200 = 135545.
Columns 18 and 19 both have period 6123600 = 2*ord(2 mod d) in a, where d is the
odd part of 18! or 19!. Of the 18 lifts of 135545 modulo 6123600, column 18 is
evil on 9 and column 19 on 6 more. The three lifts left are q mod 1890 in
41, 461 and 1826. The periodicity theorem is PanPapag's from PR 5614; the
fold by xor follows PR 8363, with the fold bases built by repeated squaring.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H3_R1
open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

private def wt (n : ℕ) := (Nat.digits 2 n).count 1

private lemma half (n : ℕ) : wt n = wt (n/2) + n%2 := by
  have h := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at h
  change wt n = wt (n/2) + wt (n%2) at h
  rw [h]
  rcases (show n%2 = 0 ∨ n%2 = 1 by omega) with e|e <;> rw [e] <;> rfl

private lemma xorParity (a b : ℕ) : wt (a ^^^ b) % 2 = (wt a+wt b) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n = 0
    · have ha : a=0 := by omega
      have hb : b=0 := by omega
      subst_vars; rfl
    have hh := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := half a
    have hb := half b
    have hab := half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hm := Nat.xor_mod_two_eq (m:=a) (n:=b)
    omega

/-- Fold bases 2^(8*2^j) built by repeated squaring, so the kernel never evaluates a huge power. -/
private def sqB : ℕ → ℕ
  | 0 => 256
  | j+1 => sqB j * sqB j

private lemma sqB_eq (j : ℕ) : sqB j = 2^(8*2^j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show sqB (j+1) = sqB j * sqB j from rfl, ih, ← pow_add, pow_succ]
    congr 1
    ring

private def foldB : ℕ → ℕ → ℕ
  | 0, n => wt n % 2
  | j+1, n => let base := sqB j; foldB j ((n/base) ^^^ (n%base))

private theorem foldB_exact (j n : ℕ) : foldB j n = wt n % 2 := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    simp only [foldB, ih, xorParity, sqB_eq]
    have h := count_ones_append (n/2^(8*2^j)) (8*2^j) (n%2^(8*2^j)) (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm

private def word18 : List (Bool × ℕ) := [(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)]

set_option maxHeartbeats 4000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    word18.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 18 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 2251799813685095) 10811) 2251799813217068) 13896581) 2251799514034442) 4853222763) 2251739610991268) 577924894832) 2247491708383319) 24871845297935) 2141571347501048) 369012649234383) 1342499907841136) 1583313975727487) 430197369060608) 1223405590579199) 1896112385589248) 0) := rfl
    _ = _ := by
      dsimp only [low,high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert18 (r : ℕ) (hr : r ∈ ([815945, 1156145, 1836545, 2176745, 2516945, 2857145, 3197345, 3537545, 4558145] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit18 (t : ℕ) (ht : 51 ≤ t) (hr : (t-51)%6123600+51 ∈ ([815945, 1156145, 1836545, 2176745, 2516945, 2857145, 3197345, 3537545, 4558145] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 18) = true := by
  apply (periodic_column (a:=t) (k:=18) (t:=51) (l:=3061800) (d:=97692469875) (z:=16)
    (ds:=word18) ht (by decide) (by decide +kernel) (by dsimp only [word18]; decide)
    (fun e => by rw [pow_add]; exact falling18 (2^e) (2^51) (by positivity) (by decide))
    (by decide)).2
  exact cert18 _ hr

private def word19 : List (Bool × ℕ) := [(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)]

set_option maxHeartbeats 4000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    word19.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 19 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 36028797018963797) 13565) 36028797018301172) 22323821) 36028796469174686) 10246937271) 36028649458260236) 1661573386472) 36014086265555045) 102417740732657) 35470875337416920) 2353125040549983) 28477269426900944) 17950712280921503) 5707543011244544) 34012249593822719) 13651808960442368) 6402373705728000) 0) := rfl
    _ = _ := by
      dsimp only [low,high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert19 (r : ℕ) (hr : r ∈ ([475745, 3877745, 4217945, 4898345, 5238545, 5578745] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit19 (t : ℕ) (ht : 55 ≤ t) (hr : (t-55)%6123600+55 ∈ ([475745, 3877745, 4217945, 4898345, 5238545, 5578745] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 19) = true := by
  apply (periodic_column (a:=t) (k:=19) (t:=55) (l:=3061800) (d:=1856156927625) (z:=16)
    (ds:=word19) ht (by decide) (by decide +kernel) (by dsimp only [word19]; decide)
    (fun e => by rw [pow_add]; exact falling19 (2^e) (2^55) (by positivity) (by decide))
    (by decide)).2
  exact cert19 _ hr

def H1 : Prop :=
  ∀ q : ℕ, q % 1890 = 41 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 1890 = 461 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 1890 = 1826 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1.H3 := by
  intro h1 h2 h3 q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  have hbig : 19 ≤ 2^(3240*q+2705) :=
    le_trans (by decide : 19 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  have hm : q % 1890 = 41 + 105 * (q / 105 % 18) := by omega
  have hlt : q / 105 % 18 < 18 := Nat.mod_lt _ (by decide)
  have k18 : (3240*q+2705-51) % 6123600 + 51 = 135545 + 340200 * (q / 105 % 18) := by omega
  have k19 : (3240*q+2705-55) % 6123600 + 55 = 135545 + 340200 * (q / 105 % 18) := by omega
  generalize q / 105 % 18 = m at hm hlt k18 k19
  interval_cases m
  · exact h1 q hm
  · exact witness _ 19 (by decide) hbig (hit19 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact h2 q hm
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 19 (by decide) hbig (hit19 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 19 (by decide) hbig (hit19 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 19 (by decide) hbig (hit19 _ (by omega) (by rw [k19]; decide))
  · exact h3 q hm

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H3_R1
