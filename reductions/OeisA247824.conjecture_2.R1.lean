import FormalConjectures.OEIS.«247824»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

/-! For the counterexample attributed to Khai-Hoan Nguyen-Dang, certify the
two prime ranks and exclude small indices using interval bounds on the prime
counting function. The larger prime is verified by Lucas's test. -/

namespace OMA.R_OeisA247824_conjecture_2_R1

open Real

-- An explicit linear bound for the indexed primes in this finite search.
private lemma nth_bound {m : ℕ} (hm : 0 < m) (big : m ≤ 1748116320732) :
    Nat.nth Nat.Prime (m-1) ≤ 64*m := by
  have i : 1 < ((64*m:ℕ):ℝ) := by exact_mod_cast (show 1 < 64*m by omega)
  have lpos := Real.log_pos i
  have l2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have num (e:ℕ) (h : 64*m+1 ≤ 2^e) : log (((64*m:ℕ):ℝ)+1) ≤ e*log 2 := by
    rw [←Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h
  have left : log ((64*m:ℕ):ℝ) ≤ log (((64*m:ℕ):ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith)
  have need : (m:ℝ)*log ((64*m:ℕ):ℝ) ≤ ((64*m:ℕ):ℝ)*log 2-log (((64*m:ℕ):ℝ)+1) := by
    by_cases sm : m < 3
    · have l := num 8 (by norm_num; omega)
      have mult := mul_le_mul_of_nonneg_left (left.trans l) (Nat.cast_nonneg (α:=ℝ) m)
      have pos : (1:ℝ)≤ m := by exact_mod_cast hm
      push_cast at *
      nlinarith only [l,mult,l2.le,mul_le_mul_of_nonneg_right pos l2.le]
    · have l := num 47 (by norm_num; omega)
      have mult := mul_le_mul_of_nonneg_left (left.trans l) (Nat.cast_nonneg (α:=ℝ) m)
      have pos : (3:ℝ)≤ m := by exact_mod_cast (show 3≤ m by omega)
      push_cast at *
      nlinarith only [l,mult,l2.le,mul_le_mul_of_nonneg_right pos l2.le]
  have pc := Chebyshev.pi_ge (64*m)
  have lb : m ≤ Nat.primeCounting (64*m) := by
    exact_mod_cast ((le_div_iff₀ lpos).mpr need).trans pc
  have lt : m-1 < Nat.count Nat.Prime (64*m+1) := by
    change m-1 < Nat.primeCounting (64*m)
    omega
  exact Nat.lt_succ_iff.mp ((Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp lt)
private lemma endpoint_prime : Nat.Prime 81744924555067 := by
  apply lucas_primality 81744924555067 (2 : ZMod 81744924555067)
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  intro q hq hd
  have fac : 81744924555067-1 = (2*3*167*51637*1579909 : ℕ) := by norm_num
  rw [fac] at hd
  simp only [hq.dvd_mul] at hd
  have eq {r : ℕ} (hr : r.Prime) (h : q ∣ r) : q = r :=
    (Nat.dvd_prime hr).mp h |>.resolve_left hq.ne_one
  rcases hd with (((h|h)|h)|h)|h
  all_goals
    have := eq (by norm_num1) h
    subst q
    norm_num only [Nat.reduceSub,Nat.reduceDiv]
    reduce_mod_char <;> decide
-- If one endpoint has too few or too many primes, the entire interval is excluded.
private lemma segment_sound {k l h m : ℕ} (pos : 0 < m) (lm : l ≤ m) (mh : m ≤ h)
    (cert : Nat.primeCounting (k*(h+1322164)-20868473) < l ∨
      h ≤ Nat.primeCounting' (k*(l+1322164)-20868473) ∨
      (l = h ∧ ¬ Nat.Prime (k*(l+1322164)-20868473))) :
    Nat.nth Nat.Prime (m-1)+20868473 ≠ k*(m+1322164) := by
  intro e
  rcases cert with bound | bound | ⟨equal,comp⟩
  · let p := Nat.nth Nat.Prime (m-1)
    have qp : k*(m+1322164)-20868473 = p := by dsimp [p]; omega
    have inc := Nat.mul_le_mul_left k (Nat.add_le_add_right mh 1322164)
    have lead : p ≤ k*(h+1322164)-20868473 := by omega
    have cnt : Nat.primeCounting p = m := by
      change Nat.count Nat.Prime (Nat.nth Nat.Prime (m-1)+1)=m
      rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]
      omega
    have le := Nat.monotone_primeCounting lead
    omega
  · let p := Nat.nth Nat.Prime (m-1)
    have qp : k*(m+1322164)-20868473 = p := by dsimp [p]; omega
    have inc := Nat.mul_le_mul_left k (Nat.add_le_add_right lm 1322164)
    have lead : k*(l+1322164)-20868473 ≤ p := by omega
    have le := Nat.monotone_primeCounting' lead
    have cnt : Nat.primeCounting' p = m-1 := Nat.primeCounting'_nth_eq _
    omega
  · have same : l = m := by omega
    rw [same] at comp
    apply comp
    rw [←e,Nat.add_sub_cancel]
    exact Nat.prime_nth_prime _
/-- Prime counts strictly below the two explicit primes give their zero-based ranks. -/
def H1 : Prop :=
  Nat.primeCounting' 20868473 = 1322163 ∧
  Nat.primeCounting' 81744924555067 = 2636932401175

/-- There are only 64 possible positive quotients. For each one, cover the
indices below the conjectured bound by prime-counting or compositeness certificates. -/
def H2 : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 64 → ∃ blocks : Finset (ℕ × ℕ),
    (∀ m : ℕ, 1 ≤ m → m < 1748116320732 → ∃ b ∈ blocks, b.1 ≤ m ∧ m ≤ b.2) ∧
    ∀ b ∈ blocks, Nat.primeCounting (k*(b.2+1322164)-20868473) < b.1 ∨
      b.2 ≤ Nat.primeCounting' (k*(b.1+1322164)-20868473) ∨
      (b.1 = b.2 ∧ ¬ Nat.Prime (k*(b.1+1322164)-20868473))

theorem main : H1 → H2 → type_of% @OeisA247824.conjecture_2 := by
  intro h₁ h₂ hall
  have p : Nat.nth Nat.Prime (1322164-1) = 20868473 := by
    have eq := Nat.nth_count (p:=Nat.Prime) (show Nat.Prime 20868473 by norm_num1)
    change Nat.nth Nat.Prime (Nat.primeCounting' 20868473) = 20868473 at eq
    simpa only [h₁.1] using eq
  have w : Nat.nth Nat.Prime (2636932401176-1) = 81744924555067 := by
    have eq := Nat.nth_count (p:=Nat.Prime) endpoint_prime
    change Nat.nth Nat.Prime (Nat.primeCounting' 81744924555067) = 81744924555067 at eq
    simpa only [h₁.2] using eq
  let S := {m : ℕ | 0 < m ∧ (m+1322164) ∣ Nat.nth Nat.Prime (m-1)+Nat.nth Nat.Prime (1322164-1)}
  have existsW : S.Nonempty := by
    refine ⟨2636932401176, by decide,31,?_⟩
    rw [w,p]
  let m := sInf S
  have hm : m ∈ S := csInf_mem existsW
  obtain ⟨pos,k,eq⟩ := hm
  have small := hall 1322164 (by decide)
  change m < 1748116320732 at small
  have nth := nth_bound pos small.le
  rw [p,mul_comm _ k] at eq
  have kpos : 1 ≤ k := by
    by_contra! zero
    have hz : k=0 := by omega
    rw [hz,zero_mul] at eq
    omega
  have ku : k ≤ 64 := by
    by_contra! high
    have mult := Nat.mul_le_mul_right (m+1322164) high
    nlinarith only [mult,nth,eq]
  obtain ⟨blocks,cover,valid⟩ := h₂ k kpos ku
  obtain ⟨b,hb,lm,mh⟩ := cover m pos small
  exact segment_sound pos lm mh (valid b hb) eq

end OMA.R_OeisA247824_conjecture_2_R1
