import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1
import Mathlib.Tactic

/-!
# Columns 17 on the classes [33, 54, 68, 96] (mod 105) of the exponents `3240*q + 2705`

Refines hypothesis H2 of OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H3.R1. Columns 17 have period 680400
in the exponent, which is `3240 * 210`, so the case split runs over `q` modulo 210. Of the
8 classes modulo 210 lying over [33, 54, 68, 96], 2 are certified here with
PanPapag's periodicity theorem and the xor-fold parity certificate; the other 6 are the hypotheses.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H2_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ q : ℕ, q % 210 ∈ ([33, 138] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 210 ∈ ([54, 159] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 210 ∈ ([68, 173] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

section Certificates

private theorem weight_half (n : ℕ) :
    (Nat.digits 2 n).count 1 = (Nat.digits 2 (n/2)).count 1 + n%2 := by
  have hh := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at hh
  change (Nat.digits 2 n).count 1 = (Nat.digits 2 (n / 2)).count 1 + (Nat.digits 2 (n % 2)).count 1 at hh
  rw [hh]
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

private theorem xor_weight (a b : ℕ) : (Nat.digits 2 (a ^^^ b)).count 1 % 2 = ((Nat.digits 2 a).count 1 + (Nat.digits 2 b).count 1) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hzero : n = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b; rfl
    have half := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := weight_half a
    have hb := weight_half b
    have hab := weight_half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hmod := Nat.xor_mod_two_eq (m := a) (n := b)
    omega

/-- Folding the two halves with xor preserves the parity and halves the bit width. -/
private theorem fold_certificate (i n : ℕ) (h :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base))) i n) = 0) :
    (Nat.digits 2 n).count 1 % 2 = 0 := by
  let count := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
  have spec (j v : ℕ) : count j v = (Nat.digits 2 v).count 1 % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let w := 8*2^j
      change count j ((v / 2^w) ^^^ (v % 2^w)) = _
      rw [ih,xor_weight]
      have hh := count_ones_append (v / 2^w) w (v%2^w) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at hh
      exact congrArg (· % 2) hh.symm
  exact (spec i n).symm.trans h


set_option maxHeartbeats 16000000 in
private theorem falling17 (x B : ℕ) (hx : 0 < x) (hB : B = 140737488355328) :
    ([(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 17 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 140737488355192) 8499) 140737488031648) 8394021) 140737331402896) 2185031419) 140714431195488) 185953177552) 139590587071800) 5374523477959) 121875921296448) 48366009233423) 53659739479424) 102992244837119) 70003205961728) 20922789888000) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity17_313745 :
    (Nat.digits 2 ((2^313745).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity17_653945 :
    (Nat.digits 2 ((2^653945).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  apply fold_certificate 21
  decide +kernel

set_option maxHeartbeats 16000000 in
private theorem column17 (a : ℕ) (ha : 47 ≤ a)
    (hr : a % 680400 ∈ ([313745, 653945] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 17) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)]
  refine (periodic_column (k := 17) (t := 47) (l := 340200) (d := 10854718875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 47]
    exact falling17 (2^w) (2^47) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr
  · rw [show (a-47) % (340200+340200) + 47 = 313745 by omega]
    exact parity17_313745
  · rw [show (a-47) % (340200+340200) + 47 = 653945 by omega]
    exact parity17_653945

end Certificates

set_option maxRecDepth 100000 in
private theorem cover : ∀ q : Fin 210, q.val % 105 ∈ ([33, 54, 68, 96] : List ℕ) →
    (3240*q.val+2705) % 680400 ∈ ([313745, 653945] : List ℕ) ∨
    q.val ∈ ([33, 138] : List ℕ) ∨
    q.val ∈ ([54, 159] : List ℕ) ∨
    q.val ∈ ([68, 173] : List ℕ) := by decide +kernel

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1.H2 := by
  intro h1 h2 h3 q hq
  have reduceMod (d : ℕ) (hd : d ∣ 680400) :
      (3240*(q%210)+2705)%d = (3240*q+2705)%d :=
    (((Nat.mod_modEq q 210).mul_left' 3240).of_dvd hd).add_right 2705
  have hq' : q % 210 % 105 ∈ ([33, 54, 68, 96] : List ℕ) := by
    rw [Nat.mod_mod_of_dvd q (by decide : 105 ∣ 210)]; exact hq
  have cases := cover ⟨q%210, Nat.mod_lt _ (by decide)⟩ hq'
  dsimp only at cases
  rw [reduceMod 680400 (by decide)] at cases
  have hbig : 32 ≤ 2^(3240*q+2705) :=
    le_trans (by decide : 32 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases cases with h | h | h | h
  · exact witness _ 17 (by decide) (by omega) (column17 _ (by omega) h)
  · exact h1 q h
  · exact h2 q h
  · exact h3 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H2_R1
