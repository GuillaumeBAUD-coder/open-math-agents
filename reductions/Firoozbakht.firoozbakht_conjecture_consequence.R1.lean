import FormalConjectures.Wikipedia.Firoozbakht
import Mathlib

/-! # From decreasing prime roots to an explicit bound for prime gaps

The analytic estimate uses a weakened form of Axler's explicit prime-counting bound. The remaining finite input only uses integers: it compares a nearby prime with a rational lower approximation to log p from the bit length of p^256. The index in the corpus starts at zero. See Kourbatov, Upper bounds for prime gaps related to Firoozbakht’s conjecture, Journal of Integer Sequences 18 (2015), Article 15.11.2. -/

namespace OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1

open Real

-- The large-prime count input is a weakened form of Axler's explicit lower bound.
def H1 : Prop := ∀ p : ℕ, 1772201 ≤ p → p.Prime →
    (p:ℝ) ≤ (p.primeCounting:ℝ) * (log p - 1 - 1/log p)

-- An integer-only finite certificate: the witness prime bounds the next gap.
def H2 : Prop := ∀ p : ℕ, 11 ≤ p → p < 1772201 → p.Prime →
    let u := 6931 * (p^256).log2
    ∃ q : ℕ, p < q ∧ q.Prime ∧
      2560000^2*(q-p) + 2560000*u < u^2


lemma root_gap {p q k : ℝ} (hp : 0<p) (hq : p<q) (hk : 0<k)
    (roots : q^(1/(k+1)) < p^(1/k)) :
    k*((q-p)/q) < log p := by
  have qp := hp.trans hq
  have lg := log_lt_log (rpow_pos_of_pos qp _) roots
  rw [log_rpow qp,log_rpow hp] at lg
  have l : k*(log q-log p) < log p := by
    field_simp at lg
    linarith
  have z := log_le_sub_one_of_pos (div_pos hp qp)
  rw [log_div hp.ne' qp.ne'] at z
  have sub : (q-p)/q ≤ log q-log p := by
    have ide : (q-p)/q = 1-p/q := by field_simp
    linarith
  exact (mul_le_mul_of_nonneg_left sub hk.le).trans_lt l

lemma log_four_le {p : ℝ} (large : 1772201 ≤ p) : (log p)^4 ≤ p ∧ 12 ≤ log p := by
  have pos : 0<p := by linarith
  have e1 : exp 1 < 3 := exp_one_lt_d9.trans (by norm_num)
  have e12 : exp 12 ≤ p := by
    rw [show exp 12 = (exp 1)^12 by simpa using exp_nat_mul 1 12]
    exact (pow_le_pow_left₀ (exp_pos 1).le e1.le 12).trans (by norm_num; linarith)
  have h12 := (le_log_iff_exp_le pos).2 e12
  have e3 : 12 ≤ exp 3 := by
    rw [show exp 3 = (exp 1)^3 by simpa using exp_nat_mul 1 3]
    have lt : (5/2:ℝ) ≤ exp 1 := le_of_lt ((by norm_num : (5/2:ℝ)<2.7182818283).trans exp_one_gt_d9)
    nlinarith [pow_le_pow_left₀ (by norm_num : 0≤(5/2:ℝ)) lt 3]
  have a := add_one_le_exp (log p/4-3)
  have w := mul_le_mul e3 a (by linarith : 0 ≤ log p/4-3+1) (exp_pos 3).le
  rw [← exp_add,show 3+(log p/4-3)=log p/4 by ring] at w
  have l : log p ≤ exp (log p/4) := by linarith
  have up := pow_le_pow_left₀ (by linarith : 0 ≤ log p) l 4
  rw [← exp_nat_mul] at up
  norm_num at up
  rw [show 4*(log p/4)=log p by ring,exp_log pos] at up
  exact ⟨up,h12⟩


lemma large_gap {p q k : ℝ} (cut : 1772201 ≤ p) (pq : p < q) (kp : 0 < k)
    (count : p ≤ k*(log p-1-1/log p)) (roots : q^(1/(k+1)) < p^(1/k)) :
    q-p < (log p)^2-log p := by
  let L := log p
  obtain ⟨four,big⟩ := log_four_le cut
  change L^4 ≤ p at four
  change 12 ≤ L at big
  change p ≤ k*(L-1-1/L) at count
  have lp : 0 < L := by linarith
  have bound : L^4 ≤ k*L := four.trans (count.trans (mul_le_mul_of_nonneg_left (by linarith [one_div_pos.mpr lp]) kp.le))
  have kl : L^3 ≤ k := (mul_le_mul_iff_left₀ lp).mp (by simpa only [← pow_succ] using bound)
  have scale := (le_div_iff₀ lp).mpr (show L^2*L ≤ k by simpa only [← pow_succ] using kl)
  have mass : p + L*(L-1) ≤ k*(L-1) := by
    rw [mul_sub,mul_one_div] at count
    linarith only [count,scale,show L*(L-1) = L^2-L by ring,lp]
  have cost := mul_le_mul_of_nonneg_right mass lp.le
  have below : L*p ≤ (k-L)*(L^2-L) := by nlinarith only [cost]
  have kp' : 0 ≤ k-L := by nlinarith [kl,show L^3 ≥ L from by nlinarith [mul_nonneg lp.le (show 0 ≤ L^2-1 by nlinarith)]]
  have pp : 0<p := by linarith
  have qpos := pp.trans pq
  have consequence := root_gap pp pq kp roots
  have cross : k*(q-p) < L*q := by
    rw [mul_div_assoc'] at consequence
    exact (div_lt_iff₀ qpos).mp consequence
  by_contra! hg
  have bad := mul_le_mul_of_nonneg_left hg kp'
  nlinarith only [bad,below,cross]


lemma finite_gap {p q : ℕ} (hp : 11 ≤ p) (pq : p < q)
    (cert : 2560000^2*(q-p) + 2560000*(6931*(p^256).log2) < (6931*(p^256).log2)^2) :
    (q:ℝ)-p < (log p)^2-log p := by
  let h := (p^256).log2
  let u : ℝ := 6931*(h:ℝ)/2560000
  have pp : 0<p := by omega
  have pr : 0<(p:ℝ) := by exact_mod_cast pp
  have pw : 2^h ≤ p^256 := Nat.log2_self_le (pow_ne_zero 256 pp.ne')
  have a : (2:ℝ)^h ≤ (p:ℝ)^256 := by exact_mod_cast pw
  have l := Real.log_le_log (by positivity) a
  rw [Real.log_pow,Real.log_pow] at l
  norm_num1 at l
  have ll : u ≤ log p := by
    have log2 : (6931/10000:ℝ) < log 2 := (by norm_num : (6931/10000:ℝ)<0.6931471803).trans Real.log_two_gt_d9
    have b := mul_le_mul_of_nonneg_left log2.le (Nat.cast_nonneg h)
    dsimp [u]
    linarith
  have base : 1 ≤ log (p:ℝ) := (le_log_iff_exp_le pr).mpr (by
    have b : (11:ℝ) ≤ p := by exact_mod_cast hp
    linarith [exp_one_lt_d9])
  have un : 0 ≤ u := by dsimp [u]; positivity
  have cv : (2560000:ℝ)^2*((q:ℝ)-p) + 2560000*(6931*(h:ℝ)) < (6931*(h:ℝ))^2 := by
    have c : ((2560000^2*(q-p)+2560000*(6931*h):ℕ):ℝ) < ((6931*h:ℕ):ℝ)^2 := by exact_mod_cast cert
    push_cast [Nat.cast_sub pq.le] at c
    norm_num1
    exact c
  have tiny : (q:ℝ)-p < u^2-u := by dsimp [u]; linarith
  nlinarith only [tiny,mul_nonneg (sub_nonneg.mpr ll) (show 0 ≤ log p + u - 1 by linarith)]


theorem main : H1 → H2 → type_of% @Firoozbakht.firoozbakht_conjecture_consequence := by
  intro count finiteCert n hn P
  let p := Nat.nth Nat.Prime n
  let q := Nat.nth Nat.Prime (n+1)
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have prime : p.Prime := Nat.prime_nth_prime n
  have pq : p<q := mono (Nat.lt_succ_self n)
  have minp : 11 ≤ p := Nat.nth_prime_four_eq_eleven ▸ mono.monotone (show 4 ≤ n by omega)
  have same : (_root_.Prime : ℕ → Prop) = Nat.Prime := funext (fun _ => propext Nat.prime_iff.symm)
  rw [same]
  change (q:ℝ) - (p:ℝ) < (log (p:ℝ))^2-log p
  by_cases cut : 1772201 ≤ p
  · have ind : p.primeCounting = n+1 := by
      change Nat.count Nat.Prime (p+1) = n+1
      rw [Nat.count_succ,if_pos prime]
      exact congrArg (·+1) (Nat.primeCounting'_nth_eq n)
    let k : ℝ := (n:ℝ)+1
    have mass : (p:ℝ) ≤ k*(log p-1-1/log p) := by simpa only [ind,Nat.cast_add,Nat.cast_one,k] using count p cut prime
    have rt := P n
    unfold Firoozbakht.firoozbakhtSeq at rt
    rw [same] at rt
    apply large_gap (by exact_mod_cast cut) (by exact_mod_cast pq) (show 0<k by dsimp [k]; positivity) mass
    simpa only [q,p,k,Nat.cast_add,Nat.cast_one] using rt
  · obtain ⟨v,hv,vp,size⟩ := finiteCert p minp (by omega) prime
    obtain ⟨i,_,e⟩ := Nat.exists_lt_card_nth_eq vp
    have lt : n < i := mono.lt_iff_lt.mp (by change p < Nat.nth Nat.Prime i; rw [e]; exact hv)
    have next : q ≤ v := e ▸ mono.monotone lt
    have qreal : (q:ℝ) ≤ v := by exact_mod_cast next
    exact lt_of_le_of_lt (sub_le_sub_right qreal _) (finite_gap minp hv size)


end OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1
