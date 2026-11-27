import OMAStatements.S_oeis_a001969
import Mathlib.Tactic

/-!
Characterization of numbers with an even number of 1-bits (OEIS A001969):
for any word, rotateRight 1 xor rotateLeft 1 has even popcount; conversely,
when n has even popcount, we explicitly construct x of odd width w = 2*m + 1
by solving the linear recurrence along odd/even bit indices.
-/

private def pxor (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => pxor f k ^^ f k

private lemma pxor_succ (f : ℕ → Bool) (k : ℕ) :
    pxor f (k + 1) = (pxor f k ^^ f k) := rfl

private lemma pxor_xor (f g : ℕ → Bool) (k : ℕ) :
    pxor (fun i => f i ^^ g i) k = (pxor f k ^^ pxor g k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pxor_succ, ih]
    cases pxor f k <;> cases pxor g k <;> cases f k <;> cases g k <;> rfl

private lemma pxor_congr {f g : ℕ → Bool} (k : ℕ) (h : ∀ i < k, f i = g i) :
    pxor f k = pxor g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pxor_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

private lemma pxor_eq_of_false_above {f : ℕ → Bool} {m k : ℕ} (hmk : m ≤ k)
    (h0 : ∀ i ≥ m, f i = false) : pxor f k = pxor f m := by
  induction k with
  | zero =>
    obtain rfl : m = 0 := by omega
    rfl
  | succ k ih =>
    by_cases hle : m ≤ k
    · simp only [pxor_succ, ih hle, h0 k hle, Bool.xor_false]
    · obtain rfl : m = k + 1 := by omega
      rfl

private lemma pxor_even_odd (f : ℕ → Bool) (m : ℕ) :
    (pxor (fun j => f (2 * j)) m ^^ pxor (fun j => f (2 * j + 1)) m) = pxor f (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2]
    simp only [pxor_succ, ← ih]
    cases pxor (fun j => f (2 * j)) m <;> cases pxor (fun j => f (2 * j + 1)) m <;>
      cases f (2 * m) <;> cases f (2 * m + 1) <;> rfl

private lemma even_sum_iff_pxor (f : ℕ → Bool) (w : ℕ) :
    Even (∑ i ∈ Finset.range w, (f i).toNat) ↔ pxor f w = false := by
  induction w with
  | zero => simp [pxor]
  | succ w ih =>
    rw [Finset.sum_range_succ, pxor_succ]
    cases hw : f w
    · simp [ih]
    · simp [Nat.even_add_one, ih]

private lemma pxor_shift (f : ℕ → Bool) (k : ℕ) :
    (pxor (fun i => f (i + 1)) k ^^ f 0) = pxor f (k + 1) := by
  induction k with
  | zero => simp [pxor]
  | succ k ih =>
    simp only [pxor_succ] at ih ⊢
    rw [← ih]
    cases pxor (fun i => f (i + 1)) k <;> cases f (k + 1) <;> cases f 0 <;> rfl

private lemma pxor_rotateRight (w : ℕ) (hw : 1 ≤ w) (word : BitVec w) :
    pxor (fun i => (word.rotateRight 1).getLsbD i) w = pxor (fun i => word.getLsbD i) w := by
  rcases Nat.eq_or_lt_of_le hw with rfl | hw2
  · simp [pxor]
  · obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
    have hmod : 1 % (k + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    have hsub : k + 2 - 1 = k + 1 := by omega
    have hlast : (word.rotateRight 1).getLsbD (k + 1) = word.getLsbD 0 := by
      simp [hmod, hsub]
    have hpref : pxor (fun i => (word.rotateRight 1).getLsbD i) (k + 1) =
        pxor (fun i => word.getLsbD (i + 1)) (k + 1) := by
      refine pxor_congr (k + 1) fun i hi => ?_
      have hi2 : i < k + 2 := by omega
      simp [hmod, hsub, hi, hi2, Nat.add_comm]
    rw [pxor_succ, hpref, hlast, pxor_shift]

private lemma pxor_rotateLeft (w : ℕ) (hw : 1 ≤ w) (word : BitVec w) :
    pxor (fun i => (word.rotateLeft 1).getLsbD i) w = pxor (fun i => word.getLsbD i) w := by
  rcases Nat.eq_or_lt_of_le hw with rfl | hw2
  · simp [pxor]
  · obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
    have hmod : 1 % (k + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    have hstep : ∀ j ≤ k + 1,
        pxor (fun i => (word.rotateLeft 1).getLsbD i) (j + 1) =
          (word.getLsbD (k + 1) ^^ pxor (fun i => word.getLsbD i) j) := by
      intro j hj
      induction j with
      | zero =>
        simp [pxor, hmod]
      | succ j ih =>
        have hlt : j + 1 < k + 2 := by omega
        have hjlt : j < k + 2 := by omega
        have hj1 : (word.rotateLeft 1).getLsbD (j + 1) = word.getLsbD j := by
          simp [hmod, hlt, hjlt]
        rw [pxor_succ, ih (by omega), hj1, pxor_succ]
        cases word.getLsbD (k + 1) <;> cases pxor (fun i => word.getLsbD i) j <;>
          cases word.getLsbD j <;> rfl
    rw [hstep (k + 1) le_rfl, Bool.xor_comm]
    rfl

private def fromBits (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Nat.bit (b 0) (fromBits (fun i => b (i + 1)) k)

private lemma fromBits_lt (b : ℕ → Bool) (k : ℕ) : fromBits b k < 2 ^ k := by
  induction k generalizing b with
  | zero => simp [fromBits]
  | succ k ih =>
    have hlt := ih (fun i => b (i + 1))
    cases hb : b 0 <;> simp [fromBits, Nat.bit, hb, Nat.pow_succ] <;> omega

private lemma testBit_fromBits (b : ℕ → Bool) (k i : ℕ) :
    (fromBits b k).testBit i = (decide (i < k) && b i) := by
  induction k generalizing b i with
  | zero => simp [fromBits]
  | succ k ih =>
    cases i with
    | zero => simp [fromBits]
    | succ i => simp [fromBits, Nat.testBit_bit_succ, ih]

theorem OMA.solution : type_of% @OMA.S_oeis_a001969.main := by
  intro n
  constructor
  · intro heven
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨0, by decide⟩
    · let m : ℕ := OMA.S_oeis_a001969.width n
      let w : ℕ := 2 * m + 1
      have hm1 : 1 ≤ m := by dsimp [m, OMA.S_oeis_a001969.width]; omega
      have hw_def : w = 2 * m + 1 := rfl
      have hlt_m : n < 2 ^ m := (Nat.log2_lt hn0).mp (by dsimp [m, OMA.S_oeis_a001969.width]; omega)
      have hn_above : ∀ i ≥ m, n.testBit i = false := by
        intro i hi
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by omega) hi))
      have hpxor_m : pxor n.testBit m = false :=
        (even_sum_iff_pxor n.testBit m).mp heven
      have hpxor_2m : pxor n.testBit (2 * m) = false := by
        rw [pxor_eq_of_false_above (by omega) hn_above, hpxor_m]
      let evenAll : Bool := pxor (fun j => n.testBit (2 * j)) m
      let b : ℕ → Bool := fun i =>
        if i % 2 = 1 then
          !(pxor (fun j => n.testBit (2 * j)) (i / 2 + 1))
        else
          !(evenAll) ^^ pxor (fun j => n.testBit (2 * j + 1)) (i / 2)
      have hb_top : b (2 * m) = true := by
        have hmod : (2 * m) % 2 = 0 := by omega
        have hdiv : (2 * m) / 2 = m := by omega
        have hne : ¬ (0 : ℕ) = 1 := by omega
        simp only [b, hmod, hdiv, hne, ite_false]
        have heo : (evenAll ^^ pxor (fun j => n.testBit (2 * j + 1)) m) = false := by
          dsimp [evenAll]
          rw [pxor_even_odd, hpxor_2m]
        cases h1 : evenAll <;> cases h2 : pxor (fun j => n.testBit (2 * j + 1)) m <;>
          simp_all
      let x : ℕ := fromBits b w
      have hx_lt : x < 2 ^ w := fromBits_lt b w
      have hx_test_top : x.testBit (2 * m) = true := by
        dsimp [x]
        rw [testBit_fromBits]
        have hlt : 2 * m < w := by omega
        simp [hlt, hb_top]
      have hx_ge : 2 ^ (2 * m) ≤ x := by
        by_contra hlt
        have htb := Nat.testBit_lt_two_pow (Nat.lt_of_not_le hlt)
        rw [hx_test_top] at htb
        cases htb
      have hx_ne : x ≠ 0 := by
        have : 1 ≤ 2 ^ (2 * m) := Nat.one_le_pow _ _ (by omega)
        omega
      have hx_log2 : x.log2 = 2 * m :=
        (Nat.log2_eq_iff hx_ne).mpr ⟨hx_ge, hx_lt⟩
      have hx_width : OMA.S_oeis_a001969.width x = w := by
        dsimp [OMA.S_oeis_a001969.width]
        omega
      refine ⟨x, ?_⟩
      unfold OMA.S_oeis_a001969.rotatedXor
      rw [hx_width]
      let word := BitVec.ofNat w x
      apply Nat.eq_of_testBit_eq
      intro i
      change (word.rotateRight 1 ^^^ word.rotateLeft 1).toNat.testBit i = n.testBit i
      rw [BitVec.testBit_toNat, BitVec.getLsbD_xor]
      by_cases hiw : i < w
      · have hmod : 1 % w = 1 := Nat.mod_eq_of_lt (by omega)
        have hsub : w - 1 = 2 * m := by omega
        have hget : ∀ j < w, word.getLsbD j = b j := by
          intro j hj
          dsimp [word, x]
          rw [BitVec.getLsbD_ofNat, testBit_fromBits]
          simp [hj]
        have h01 : ¬ (0 : ℕ) = 1 := by omega
        by_cases hi0 : i = 0
        · subst hi0
          have h1w : 1 < w := by omega
          have h2mw : 2 * m < w := by omega
          rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]
          simp only [hmod, hsub, show 0 < 2 * m by omega, ↓reduceIte,
            show 0 < 1 by omega, Nat.add_zero, hget 1 h1w, hget (2 * m) h2mw, hb_top]
          have hb1 : b 1 = !n.testBit 0 := by
            simp [b, pxor]
          rw [hb1]
          cases n.testBit 0 <;> rfl
        · by_cases hitop : i = 2 * m
          · subst hitop
            have h0w : 0 < w := by omega
            have hpredw : 2 * m - 1 < w := by omega
            rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]
            simp only [hmod, hsub, show ¬ (2 * m < 2 * m) by omega,
              show ¬ (2 * m < 1) by omega, ite_false, decide_eq_true hiw, Bool.true_and,
              show 2 * m - 2 * m = 0 by omega, hget 0 h0w, hget (2 * m - 1) hpredw]
            have hb0 : b 0 = !evenAll := by
              simp [b, pxor]
            have hbm : b (2 * m - 1) = !evenAll := by
              have hhm : (2 * m - 1) % 2 = 1 := by omega
              have hhd : (2 * m - 1) / 2 + 1 = m := by omega
              simp only [b, hhm, ↓reduceIte, hhd]
              rfl
            rw [hb0, hbm, hn_above (2 * m) (by omega)]
            cases evenAll <;> rfl
          · have hi_lt : i < 2 * m := by omega
            have hi1_lt : i + 1 < w := by omega
            have hip_lt : i - 1 < w := by omega
            rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]
            simp only [hmod, hsub, show i < 2 * m by omega,
              show ¬ (i < 1) by omega, ↓reduceIte, decide_eq_true hiw, Bool.true_and,
              show 1 + i = i + 1 by omega, hget (i + 1) hi1_lt, hget (i - 1) hip_lt]
            rcases Nat.even_or_odd' i with ⟨k, hk | hk⟩
            · subst hk
              have hk0 : 1 ≤ k := by omega
              have h1m : (2 * k + 1) % 2 = 1 := by omega
              have h1d : (2 * k + 1) / 2 + 1 = k + 1 := by omega
              have h2m : (2 * k - 1) % 2 = 1 := by omega
              have h2d : (2 * k - 1) / 2 + 1 = k := by omega
              simp only [b, h1m, h2m, ↓reduceIte]
              rw [h1d, h2d, pxor_succ]
              cases pxor (fun j => n.testBit (2 * j)) k <;> cases n.testBit (2 * k) <;> rfl
            · subst hk
              have h1m : (2 * k + 1 + 1) % 2 = 0 := by omega
              have h1d : (2 * k + 1 + 1) / 2 = k + 1 := by omega
              have h2m : (2 * k + 1 - 1) % 2 = 0 := by omega
              have h2d : (2 * k + 1 - 1) / 2 = k := by omega
              simp only [b, h1m, h2m, h01, ite_false]
              rw [h1d, h2d, pxor_succ]
              cases evenAll <;> cases pxor (fun j => n.testBit (2 * j + 1)) k <;>
                cases n.testBit (2 * k + 1) <;> rfl
      · have hlhs : (word.rotateRight 1 ^^^ word.rotateLeft 1).getLsbD i = false := by
          rw [← BitVec.testBit_toNat]
          exact Nat.testBit_lt_two_pow
            (lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by omega) (by omega)))
        have hnw : m ≤ i := by omega
        rw [← BitVec.getLsbD_xor, hlhs, hn_above i hnw]
  · rintro ⟨x, hx⟩
    subst hx
    let w : ℕ := OMA.S_oeis_a001969.width x
    let word : BitVec w := BitVec.ofNat w x
    let res : BitVec w := word.rotateRight 1 ^^^ word.rotateLeft 1
    have hlt_w : res.toNat < 2 ^ w := BitVec.isLt res
    have hwid_le : OMA.S_oeis_a001969.width res.toNat ≤ w := by
      by_cases h0 : res.toNat = 0
      · dsimp [OMA.S_oeis_a001969.width]
        rw [h0, show Nat.log2 0 = 0 by decide]
        dsimp [w, OMA.S_oeis_a001969.width]
        exact Nat.succ_le_succ (Nat.zero_le _)
      · dsimp [OMA.S_oeis_a001969.width]
        exact (Nat.log2_lt h0).mpr hlt_w
    have hres_above : ∀ i ≥ OMA.S_oeis_a001969.width res.toNat, res.toNat.testBit i = false := by
      intro i hi
      by_cases h0 : res.toNat = 0
      · simp [h0]
      · have hlt : res.toNat < 2 ^ OMA.S_oeis_a001969.width res.toNat :=
          (Nat.log2_lt h0).mp (by dsimp [OMA.S_oeis_a001969.width]; omega)
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hi))
    have hpxor_w : pxor res.toNat.testBit w = false := by
      have hw1 : 1 ≤ w := by dsimp [w, OMA.S_oeis_a001969.width]; omega
      have hcon : pxor res.toNat.testBit w =
          pxor (fun i => (word.rotateRight 1).getLsbD i ^^ (word.rotateLeft 1).getLsbD i) w := by
        refine pxor_congr w fun i _ => ?_
        rw [BitVec.testBit_toNat, BitVec.getLsbD_xor]
      rw [hcon, pxor_xor, pxor_rotateRight w hw1 word, pxor_rotateLeft w hw1 word, Bool.xor_self]
    unfold OMA.S_oeis_a001969.ones
    rw [even_sum_iff_pxor]
    change pxor res.toNat.testBit (OMA.S_oeis_a001969.width res.toNat) = false
    rw [← pxor_eq_of_false_above hwid_le hres_above]
    exact hpxor_w
