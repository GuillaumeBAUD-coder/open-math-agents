import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Even rows with an odd part greater than one

For `n = 2^a * m` with `m ≤ 2^a`, the binary weight of the second
coefficient is the weight of `m*m-1`, plus `a`, minus the weight of `m-1`.
The low `a` bits are the padded complement of `m-1`, and the final
`a-1` zero bits do not affect the weight. A kernel-checked search in
columns 2 through 9 also covers all eligible rows below 256.

The proof of binary concatenation follows PanPapag's reduction for odd
exponents. The finite parity check uses the XOR folding technique of PR 38919.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H2_R1

private theorem count_ones_append (x w c : ℕ) (hc : c < 2^w) :
    (Nat.digits 2 (x * 2^w + c)).count 1 =
      (Nat.digits 2 x).count 1 + (Nat.digits 2 c).count 1 := by
  have hlen : (Nat.digits 2 c).length ≤ w :=
    (Nat.digits_length_le_iff (by decide : 1 < 2) _).mpr hc
  by_cases hx : x = 0
  · simp [hx]
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (m := x) (n := c)
    (k := w - (Nat.digits 2 c).length) (by decide) (Nat.pos_of_ne_zero hx)
  rw [show (Nat.digits 2 c).length + (w - (Nat.digits 2 c).length) = w by omega] at h
  rw [show x * 2^w + c = c + 2^w*x by ring, ← h]
  simp [List.count_replicate, Nat.add_comm]

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

/-- Fold the halves with xor until only one byte remains. -/
private def foldParity : ℕ → ℕ → ℕ
  | 0, v => (Nat.digits 2 v).count 1 % 2
  | j+1, v =>
    let w := 8 * 2^j
    foldParity j ((v >>> w) ^^^ (v &&& ((1 <<< w)-1)))

private theorem foldParity_eq (j v : ℕ) :
    foldParity j v = (Nat.digits 2 v).count 1 % 2 := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    change foldParity j ((v >>> (8 * 2^j)) ^^^ (v &&& ((1 <<< (8 * 2^j))-1))) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow,
      Nat.and_two_pow_sub_one_eq_mod, ih, xor_weight]
    have h := count_ones_append (v / 2^(8*2^j)) (8*2^j) (v % 2^(8*2^j))
      (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm

private def smallWitness (n k : ℕ) : Bool :=
  decide (k < n) && (foldParity 4 (n.descFactorial k / k.factorial) == 0)

private def checkResidues (rs : List ℕ) : Bool :=
  rs.all fun n =>
    (n % 2 == 1) || (foldParity 4 n == 0) || (n == 2^n.log2) ||
      (List.range' 2 8).any (smallWitness n)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem checkedSmall : checkResidues (List.range 256) = true := by decide +kernel

private theorem small_rows (n : ℕ) (hn : n < 256) (he : Even n)
    (hm : OeisA249609.isEvil n = false) (hp : ∀ a : ℕ, n ≠ 2^a) :
    ∃ k ∈ List.range' 1 n, OeisA249609.isEvil (n.choose k) = true := by
  have h := List.all_eq_true.mp checkedSmall n (List.mem_range.mpr hn)
  change ((n % 2 == 1) || (foldParity 4 n == 0) || (n == 2^n.log2) ||
    (List.range' 2 8).any (smallWitness n)) = true at h
  have hpar : (foldParity 4 n == 0) = false := by
    simpa only [foldParity_eq, OeisA249609.isEvil] using hm
  simp [Nat.even_iff.mp he, hpar, hp n.log2] at h
  obtain ⟨k, ⟨hkpos, _⟩, hw⟩ := h
  simp only [smallWitness, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, foldParity_eq,
    ← Nat.choose_eq_descFactorial_div_factorial] at hw
  exact ⟨k, List.mem_range'_1.mpr ⟨by omega, by omega⟩, by
    simp [OeisA249609.isEvil, hw.2]⟩

private theorem shift_weight (a m : ℕ) (hm : 0 < m) :
    (Nat.digits 2 (2^a*m)).count 1 = (Nat.digits 2 m).count 1 := by
  rw [Nat.digits_base_pow_mul (by decide) hm]
  simp [List.count_replicate]

private theorem complement_weight (a x : ℕ) (hx : x < 2^a) :
    (Nat.digits 2 (2^a-1-x)).count 1 + (Nat.digits 2 x).count 1 = a := by
  induction a generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst x
    decide
  | succ a ih =>
    rw [pow_succ] at hx
    have hhalf : x/2 < 2^a := by omega
    have hcomp : (2^(a+1)-1-x)/2 = 2^a-1-x/2 := by rw [pow_succ]; omega
    have hbit : (2^(a+1)-1-x)%2 + x%2 = 1 := by rw [pow_succ]; omega
    rw [weight_half (2^(a+1)-1-x), weight_half x, hcomp]
    have h := ih (x/2) hhalf
    omega

/-- The second coefficient has a fixed high part and a complemented suffix. -/
theorem second_column_weight (a m : ℕ) (ha : 0 < a) (hm : 1 < m) (hw : m ≤ 2^a) :
    (Nat.digits 2 ((2^a*m).choose 2)).count 1 + (Nat.digits 2 (m-1)).count 1 =
      (Nat.digits 2 (m*m-1)).count 1 + a := by
  let v := m * (2^a*m-1)
  have hv : 0 < v := by
    have hpow : 0 < 2^a := by positivity
    have hmul : 2^a ≤ 2^a*m := Nat.le_mul_of_pos_right _ (by omega)
    have htwo : 2 ≤ 2^a := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ a by omega)
    exact Nat.mul_pos (by omega) (by omega)
  have he : (2^a*m).choose 2 = 2^(a-1)*v := by
    rw [Nat.choose_two_right]
    have hpow : 2^a = 2^(a-1)*2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hfactor : 2^a*m*(2^a*m-1) = (2^(a-1)*v)*2 := by
      unfold v
      calc
        _ = (2^(a-1)*2)*m*(2^a*m-1) := by nth_rw 1 [hpow]
        _ = _ := by ring
    rw [hfactor]
    simp
  have hj : v = (m*m-1)*2^a+(2^a-m) := by
    have hmSq : 1 ≤ m*m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hn : 1 ≤ 2^a*m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hleft : v + m = m*(2^a*m) := by
      calc
        _ = m*((2^a*m-1)+1) := by simp [v, Nat.mul_add]
        _ = _ := by rw [Nat.sub_add_cancel hn]
    have hright : (m*m-1)*2^a+(2^a-m)+m = m*(2^a*m) := by
      rw [Nat.add_assoc, Nat.sub_add_cancel hw]
      calc
        _ = ((m*m-1)+1)*2^a := by rw [Nat.add_mul, Nat.one_mul]
        _ = _ := by rw [Nat.sub_add_cancel hmSq]; ring
    exact Nat.add_right_cancel (hleft.trans hright.symm)
  have hs : 2^a-m < 2^a := Nat.sub_lt (by positivity) (by omega)
  have hc := complement_weight a (m-1) (by omega)
  have hlow : 2^a-m = 2^a-1-(m-1) := by omega
  rw [he, shift_weight _ _ hv, hj, count_ones_append _ _ _ hs, hlow]
  omega

/-- Large rows where the odd part does not fit in the trailing zero bits. -/
def H1 : Prop :=
  ∀ a m : ℕ, 0 < a → 1 < m → Odd m → OeisA249609.isEvil m = false →
    256 ≤ 2^a*m → 2^a < m →
    ∃ k ∈ List.range' 1 (2^a*m), OeisA249609.isEvil ((2^a*m).choose k) = true

/-- Large rows with a fitting odd part and unfavorable second-column parity. -/
def H2 : Prop :=
  ∀ a m : ℕ, 0 < a → 1 < m → Odd m → OeisA249609.isEvil m = false →
    256 ≤ 2^a*m → m ≤ 2^a →
    ((Nat.digits 2 (m*m-1)).count 1 + a) % 2 ≠ (Nat.digits 2 (m-1)).count 1 % 2 →
    ∃ k ∈ List.range' 1 (2^a*m), OeisA249609.isEvil ((2^a*m).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1.H2 := by
  intro h1 h2 n hn he hm _ hp
  by_cases hsmall : n < 256
  · exact small_rows n hsmall he hm hp
  obtain ⟨a, m, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have ha : 0 < a := by
    by_contra ha
    have : a = 0 := by omega
    subst a
    simp at he
    exact (Nat.not_even_iff_odd.mpr hodd) he
  have hmpos : 0 < m := hodd.pos
  have hmgt : 1 < m := by
    by_contra h
    have : m = 1 := by omega
    exact hp a (by simp [this])
  have hoddPart : OeisA249609.isEvil m = false := by
    simpa only [OeisA249609.isEvil, shift_weight a m hmpos] using hm
  by_cases hw : m ≤ 2^a
  · by_cases hpar : ((Nat.digits 2 (m*m-1)).count 1 + a) % 2 =
        (Nat.digits 2 (m-1)).count 1 % 2
    · have hwgt := second_column_weight a m ha hmgt hw
      refine ⟨2, List.mem_range'_1.mpr ⟨by decide, by omega⟩, ?_⟩
      have hzero : (Nat.digits 2 ((2^a*m).choose 2)).count 1 % 2 = 0 := by omega
      simp [OeisA249609.isEvil, hzero]
    · exact h2 a m ha hmgt hodd hoddPart (by omega) hw hpar
  · exact h1 a m ha hmgt hodd hoddPart (by omega) (by omega)

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H2_R1
