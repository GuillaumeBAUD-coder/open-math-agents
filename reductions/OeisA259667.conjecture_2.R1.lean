import FormalConjectures.OEIS.«259667»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Multiplicity

/-!
# Catalan residues and ternary digits of powers of two

Credit: @marcusbuffett

Lucas's theorem gives the exact equivalence between a Catalan residue of 5
at index 2^k-1 and a positive exponent k for which 2^k omits the digit 2.
This identifies the question with the strong Erdős ternary digit conjecture.
The joint digit test for residues 1 and 5 was noted by Jianing Song in A259667.

The count on intervals of length 2·3^d is an elementary version of the
Narkiewicz exponent log₃(2). The finite check lifts admissible exponents
one base-three digit at a time, following the method of Robert I. Saye,
On Two Conjectures Concerning the Ternary Digits of Powers of Two,
J. Integer Sequences 25 (2022), https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.html.
This file verifies the prefix k < 2·3^15 in the Lean kernel. Saye's
published computation up to 2·3^45 motivates the boundary between the
remaining finite verification and the open tail.
-/

namespace CatalanTernary

open Nat

private lemma cb3 (n : ℕ) : n.centralBinom % 3 =
    if 2 ∈ digits 3 n then 0 else if n%2 = 0 then 1 else 2 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · decide
    have step := ih (n/3) (Nat.div_lt_self hn (by decide))
    have luc : n.centralBinom % 3 =
        (((2*n)%3).choose (n%3) * ((2*n)/3).choose (n/3)) % 3 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [luc, Nat.digits_def' (by decide) hn]
    simp only [List.mem_cons]
    rcases (show n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 by omega) with r | r | r
    · have h : (2*n)/3 = 2*(n/3) := by omega
      rw [r,h,show (2*n)%3=0 by omega]
      simp only [Nat.choose_zero_right, one_mul, Nat.reduceEqDiff, false_or]
      exact step.trans (by rw [show n%2=(n/3)%2 by omega])
    · rw [r,show (2*n)/3 = 2*(n/3) by omega, show (2*n)%3=2 by omega]
      change (2*(n/3).centralBinom)%3 = _
      rw [Nat.mul_mod, step]
      by_cases d : 2 ∈ digits 3 (n/3) <;> by_cases e : (n/3)%2=0 <;>
        simp [d,e, show n%2 = (if (n/3)%2=0 then 1 else 0) by split <;> omega]
    · rw [r,show (2*n)%3=1 by omega]
      simp

private lemma chooseOdd (k j : ℕ) (hj : j < 2^k) :
    (2^k-1).choose j % 2 = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  induction k generalizing j with
  | zero =>
    have : j=0 := by simpa using hj
    subst j
    decide
  | succ k ih =>
    have p : 0 < 2^k := by positivity
    have luc : (2^(k+1)-1).choose j % 2 =
      (((2^(k+1)-1)%2).choose (j%2) * ((2^(k+1)-1)/2).choose (j/2)) % 2 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [pow_succ] at hj luc ⊢
    rw [luc,show (2^k*2-1)%2=1 by omega,show (2^k*2-1)/2=2^k-1 by omega]
    have one : (1:ℕ).choose (j%2) = 1 := by
      rcases (show j%2=0 ∨ j%2=1 by omega) with e|e <;> rw [e] <;> decide
    rw [one, one_mul, ih (j/2) (by omega)]

private lemma catOdd (k : ℕ) : catalan (2^k-1) % 2 = 1 := by
  let n := 2^k-1
  have pos : 0<2^k := by positivity
  have h : (2*n+1)*catalan n = (2*n+1).choose (n+1) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n)
    calc
      (2*n+1)*catalan n*(n+1) = (2*n+1)*n.centralBinom := by
        rw [← succ_mul_catalan_eq_centralBinom]; ring
      _ = _ := Nat.add_one_mul_choose_eq (2*n) n
  have eq : 2*n+1 = 2^(k+1)-1 := by dsimp [n]; rw [pow_succ]; omega
  have c := chooseOdd (k+1) (n+1) (by dsimp [n]; rw [pow_succ]; omega)
  rw [← eq, ← h, Nat.mul_mod, show (2*n+1)%2=1 by omega,one_mul,Nat.mod_mod] at c
  exact c

private lemma twoModThree (k : ℕ) : 2^k%3 = (if k%2=0 then 1 else 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split <;> split <;> first | decide | omega

theorem catFive (k : ℕ) :
    OeisA259667.a (2^k-1) = 5 ↔ 0 < k ∧ 2 ∉ digits 3 (2^k) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [OeisA259667.a_0]
  let n := 2^k-1
  have pn : 1 < 2^k := one_lt_pow₀ (by decide) hk.ne'
  have e : n+1 = 2^k := by dsimp [n]; omega
  have e2 : 2^k % 2 = 0 := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'; simp [pow_succ]
  have p2 : n%2=1 := by dsimp [n]; omega
  have eq := congrArg (· % 3) (succ_mul_catalan_eq_centralBinom n)
  change ((n+1)*catalan n)%3 = n.centralBinom%3 at eq
  rw [Nat.mul_mod, e, twoModThree, cb3, if_neg (by omega : ¬n%2=0)] at eq
  have odd := catOdd k
  change catalan n % 2 = 1 at odd
  change catalan n%6 = 5 ↔ _
  rw [Nat.digits_def' (by decide) (show 0<2^k by omega), List.mem_cons, twoModThree]
  have dig : digits 3 n = n%3 :: digits 3 (n/3) := Nat.digits_def' (by decide) (by omega)
  simp only [dig, List.mem_cons] at eq
  have z := twoModThree k
  have q : n/3 = 2^k/3 := by split at z <;> omega
  rw [q] at eq
  have con : catalan n % 3 = (catalan n % 6) % 3 := (Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 6)).symm
  rw [con] at eq
  have cmax := Nat.mod_lt (catalan n) (by decide : 0<6)
  by_cases even : k%2=0 <;> by_cases bad : 2 ∈ digits 3 (2^k/3) <;>
    simp [even,bad,hk] at eq z ⊢ <;> (try split_ifs at eq) <;> omega


private lemma rangePow (d t : ℕ) : 4^t ≡ 1 [MOD 3^(d+1)] ↔ 3^d ∣ t := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  rcases t.eq_zero_or_pos with rfl | ht
  · simp [Nat.ModEq]
  have big : 1 < 4^t := one_lt_pow₀ (by decide) ht.ne'
  have h := padicValNat.pow_sub_pow (p:=3) (x:=4) (y:=1) (by decide) (by decide)
    (by decide) (by decide) ht.ne'
  simp at h
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' big.le, padicValNat_dvd_iff_le (by omega),
    padicValNat_dvd_iff_le ht.ne']
  omega

private lemma powerInj (d i j : ℕ) (hi : i < 3^d) (hj : j < 3^d)
    (eq : 4^i ≡ 4^j [MOD 3^(d+1)]) : i = j := by
  wlog h : i ≤ j generalizing i j
  · exact (this j i hj hi eq.symm (by omega)).symm
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
  have cop : Nat.Coprime (3^(d+1)) (4^i) := ((by decide : Nat.Coprime 3 4).pow_left _).pow_right _
  have eq' : 4^i * 4^t ≡ 4^i*1 [MOD 3^(d+1)] := by simpa [pow_add] using eq.symm
  have dvt := (rangePow d t).mp (Nat.ModEq.cancel_left_of_coprime cop eq')
  by_contra! ne
  have := Nat.le_of_dvd (show 0<t by omega) dvt
  omega

private lemma digitLt (n : ℕ) (h : 2 ∉ digits 3 n) :
    n%3 < 2 ∧ 2 ∉ digits 3 (n/3) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · decide
  rw [Nat.digits_def' (by decide) hn, List.mem_cons, not_or] at h
  exact ⟨by have := h.1; omega, h.2⟩

-- A discrete version of the Narkiewicz count. There are at most 2^d
-- exceptions in the first 2*3^d exponents.
theorem countFive (d : ℕ) :
    ((Finset.range (2*3^d)).filter (fun k => OeisA259667.a (2^k-1)=5)).card ≤ 2^d := by
  classical
  let good : ℕ → Finset ℕ := Nat.rec {0} (fun _ S =>
    S.image (fun n=>3*n) ∪ S.image (fun n=>3*n+1))
  have card (s : ℕ) : (good s).card ≤ 2^s := by
    induction s with
    | zero => simp [good]
    | succ s ih =>
      change Finset.card ((good s).image (fun x => 3*x) ∪ (good s).image (fun x => 3*x+1)) ≤ _
      calc
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ (good s).card + (good s).card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ _ := by rw [pow_succ]; omega
  have mem (s n : ℕ) (h : 2 ∉ digits 3 n) : n%3^s ∈ good s := by
    induction s generalizing n with
    | zero => simp [good, Nat.mod_one]
    | succ s ih =>
      obtain ⟨h₁,h₂⟩ := digitLt n h
      have hq := ih (n/3) h₂
      change _ ∈ _ ∪ _
      rw [_root_.pow_succ', Nat.mod_mul]
      rcases (show n%3=0 ∨ n%3=1 by omega) with h|h
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hq, by simp [h]⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hq, by simp [h,add_comm]⟩)
  let f (k : ℕ) := (2^k/3)%3^d
  have data (k : ℕ) (hk : k ∈ (Finset.range (2*3^d)).filter (fun k => OeisA259667.a (2^k-1)=5)) :
      k < 2*3^d ∧ k%2=0 ∧ 2^k%3=1 ∧ 2 ∉ digits 3 (2^k) := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hk
    obtain ⟨-,hz⟩ := (catFive k).mp h₂
    have a := twoModThree k
    have b := (digitLt _ hz).1
    split at a <;> simp_all
  apply le_trans (Finset.card_le_card_of_injOn (t:=good d) f ?_ ?_) (card d)
  · intro k hk
    exact mem _ _ (digitLt _ (data k hk).2.2.2).2
  · intro k hk l hl eq
    obtain ⟨ks,ke,ku,-⟩ := data k hk
    obtain ⟨ls,le,lu,-⟩ := data l hl
    have e : 2^k ≡ 2^l [MOD 3^(d+1)] := by
      change _ % _ = _ % _
      rw [_root_.pow_succ', Nat.mod_mul, Nat.mod_mul, ku, lu]
      exact congrArg (fun x => 1+3*x) eq
    have rewritePow (x : ℕ) (h : x%2=0) : 2^x = 4^(x/2) := by
      calc
        2^x = 2^(2*(x/2)) := congrArg (2^·) (by omega)
        _ = _ := by rw [pow_mul]; rfl
    rw [rewritePow k ke, rewritePow l le] at e
    have eq' := powerInj d (k/2) (l/2) (by omega) (by omega) e
    omega


private lemma noTwoDiv {x : ℕ} (h : 2 ∉ digits 3 x) (j : ℕ) :
    2 ∉ digits 3 (x/3^j) := by
  induction j with
  | zero => simpa using h
  | succ j ih => simpa [pow_succ,Nat.div_div_eq_div_mul] using (digitLt _ ih).2

private lemma noTwoMod {x : ℕ} (h : 2 ∉ digits 3 x) (j : ℕ) :
    2 ∉ digits 3 (x%3^j) := by
  induction j generalizing x with
  | zero => simp [Nat.mod_one]
  | succ j ih =>
    rcases (x%3^(j+1)).eq_zero_or_pos with z|hp
    · simp [z]
    rw [Nat.digits_def' (by decide) hp,List.mem_cons,not_or]
    rw [_root_.pow_succ', Nat.mod_mod_of_dvd _ (dvd_mul_right _ _),
      Nat.mod_mul_right_div_self]
    exact ⟨by have := (digitLt x h).1; omega, ih (digitLt x h).2⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private lemma checkedPrefix (j : ℕ) (hj : j < 3^15) (h : 2 ∉ digits 3 (4^j)) :
    j = 0 ∨ j = 1 ∨ j = 4 := by
  let M : ℕ := 3^64
  let hasTwo : ℕ → ℕ → Bool := Nat.rec (fun _ => false)
    (fun _ next x => decide (x%3=2) || next (x/3))
  have safe (s x : ℕ) (h : 2 ∉ digits 3 x) : hasTwo s x = false := by
    induction s generalizing x with
    | zero => rfl
    | succ s ih =>
      change (decide (x%3=2) || hasTwo s (x/3)) = false
      have u := digitLt x h
      simp [show x%3≠2 by omega,ih _ u.2]
  let scan : ℕ → ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec
    (fun q idx v _ => decide (idx=0 ∨ idx=1 ∨ idx=4) || hasTwo 48 (v/q))
    (fun _ next q idx v u =>
      decide ((v/q)%3=2) || [0,1,2].all (fun i =>
        next (q*3) (idx+q*i) ((v*u^i)%M) (u^3%M)))
  have sound (dep lev idx v u t : ℕ) (bound : lev+dep ≤ 64)
      (hv : v = 4^idx%M) (hu : u=4^(3^lev)%M)
      (ht : t<3^dep) (good : 2 ∉ digits 3 (4^(idx+3^lev*t)))
      (ok : scan dep (3^lev) idx v u = true) :
      idx+3^lev*t=0 ∨ idx+3^lev*t=1 ∨ idx+3^lev*t=4 := by
    induction dep generalizing lev idx v u t with
    | zero =>
      have t0 : t=0 := by simpa using ht
      subst t
      simp only [Nat.mul_zero, Nat.add_zero] at good ⊢
      change (decide (idx=0 ∨ idx=1 ∨ idx=4) || hasTwo 48 (v/3^lev)) = true at ok
      rw [hv, safe _ _ (noTwoDiv (noTwoMod good 64) lev)] at ok
      simpa using ok
    | succ dep ih =>
      let q := 3^lev
      let i := t%3
      have idxEq : idx+3^lev*t = (idx+q*i)+3^(lev+1)*(t/3) := by
        dsimp [q,i]; rw [pow_succ]; linear_combination 3^lev * (Nat.mod_add_div t 3).symm
      have sub : 3^(lev+1) ∣ M := pow_dvd_pow _ (by omega : lev+1 ≤ 64)
      have base : 4^(idx+3^lev*t) ≡ 4^idx [MOD 3^(lev+1)] := by
        have per := ((rangePow lev (3^lev)).mpr dvd_rfl).pow t
        simpa [pow_add, pow_mul] using per.mul_left (4^idx)
      have same := base.trans (((Nat.mod_modEq (4^idx) M).of_dvd sub).symm)
      change _%_ = _%_ at same
      have digit := congrArg (·/3^lev) same
      simp only [pow_succ, Nat.mod_mul_right_div_self] at digit
      have notBad : (v/q)%3 ≠ 2 := by
        rw [hv]; dsimp [q]
        have := (digitLt _ (noTwoDiv good lev)).1
        omega
      change (decide ((v/q)%3=2) || [0,1,2].all _) = true at ok
      simp only [notBad,decide_false,Bool.false_or,List.all_eq_true] at ok
      have imem : i ∈ ([0,1,2]:List ℕ) := by dsimp [i]; simp; omega
      have next := ok i imem
      have vi : (v*u^i)%M = 4^(idx+q*i)%M := by
        rw [hv,hu,pow_add,pow_mul]
        exact (((Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow i)) : _)
      have ui : u^3%M = 4^(3^(lev+1))%M := by
        rw [hu, pow_succ (3:ℕ) lev, pow_mul]
        exact (Nat.mod_modEq _ _).pow 3
      rw [idxEq] at good ⊢
      have ht1 : t/3 < 3^dep := by rw [pow_succ] at ht; omega
      exact ih (lev+1) (idx+q*i) _ _ (t/3) (by omega) vi ui ht1 good
        (by simpa only [q, pow_succ (3:ℕ) lev] using next)
  have all : scan 15 1 0 1 4 = true := by
    dsimp only [scan,hasTwo,M]
    decide +kernel
  simpa using sound 15 0 0 1 4 j (by decide) (by decide) (by decide) hj (by simpa using h) all


end CatalanTernary

namespace OMA.R_OeisA259667_conjecture_2_R1

/-- The rest of the finite range reported in Saye's 2022 computation. -/
def H1 : Prop := ∀ j : ℕ, 3^15 ≤ j → j ≤ 3^45 → 2 ∈ Nat.digits 3 (4^j)

/-- The open tail of the Erdős ternary digit conjecture. -/
def H2 : Prop := ∀ j : ℕ, 3^45 < j → 2 ∈ Nat.digits 3 (4^j)

theorem main : H1 → H2 → type_of% @OeisA259667.conjecture_2 := by
  intro verified tail k
  rw [CatalanTernary.catFive]
  constructor
  · rintro ⟨pos,noTwo⟩
    have lo := (CatalanTernary.digitLt _ noTwo).1
    have z := CatalanTernary.twoModThree k
    have even : k%2=0 := by split at z <;> omega
    let j := k/2
    have ek : k = 2*j := by dsimp [j]; omega
    have ej : 2^k = 4^j := by calc
      2^k = 2^(2*j) := congrArg (2^·) ek
      _ = _ := by rw [pow_mul]; rfl
    rw [ej] at noTwo
    by_cases small : j < 3^15
    · obtain e|e|e := CatalanTernary.checkedPrefix j small noTwo <;> omega
    by_cases mid : j ≤ 3^45
    · exact False.elim (noTwo (verified j (by omega) mid))
    · exact False.elim (noTwo (tail j (by omega)))
  · rintro (rfl|rfl) <;> decide

end OMA.R_OeisA259667_conjecture_2_R1
