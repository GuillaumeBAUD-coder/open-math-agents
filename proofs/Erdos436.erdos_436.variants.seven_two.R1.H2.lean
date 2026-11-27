import OMAReductions.R_Erdos436_erdos_436_variants_seven_two_R1
import Mathlib

/-! For an odd modulus each prime costs at least five to the power of its case-vector weight. An odd zero below the cutoff has total weight zero or seven. Removing a prime from its factorization bounds it by 105 for weight one and by 527 for weight two. The bounded search visits nondecreasing factor lists and checks their even neighbors. -/
namespace Odd436
open Nat Finset
def mark (p : ℕ) : ℕ := if p ∈ ([3,41] : List ℕ) then 0 else
  if p ∈ ([79,137,197,233,269,277,463,467,797,1709,2647,2903,15791] : List ℕ) then 2 else 1
def score (l : List ℕ) := (l.map mark).sum
def nz (n : ℕ) : Bool := score n.primeFactorsList % 7 != 0
def primes : List ℕ :=
  [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,137,197,233,269,277,463,467]
def neighbors (x w : ℕ) : Bool :=
  w % 7 != 0 || ((x ≤ 1 || nz (x-1)) && (1649375 ≤ x || nz (x+1)))
def explore : ℕ → ℕ → ℕ → ℕ → Bool
  | 0,x,w,_ => neighbors x w
  | k+1,x,w,low => neighbors x w && primes.all (fun p =>
      if low ≤ p ∧ x*p ≤ 1649375 ∧ (w+mark p = 0 ∨
        (w+mark p ≤ 7 ∧ (x*p)*5^(7-(w+mark p)) ≤ 1649375)) then explore k (x*p) (w+mark p) p else true)

private theorem mark_le (p : ℕ) : mark p ≤ 2 := by unfold mark; split_ifs <;> decide

private theorem power_cost (p : ℕ) (hp : p.Prime) (ho : p ≠ 2) : 5 ^ mark p ≤ p := by
  by_cases h : p < 25
  · have tab : ∀ i : Fin 25, i.val.Prime → i.val ≠ 2 → 5 ^ mark i.val ≤ i.val := by decide +kernel
    exact tab ⟨p,h⟩ hp ho
  · exact (Nat.pow_le_pow_right (by decide : 0 < 5) (mark_le p)).trans (by omega)

private theorem prod_lower (b : ℕ) (v : ℕ → ℕ) (s : List ℕ)
    (h : ∀ p ∈ s, b ^ v p ≤ p) : b ^ (s.map v).sum ≤ s.prod := by
  induction s with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
    exact Nat.mul_le_mul (h p (by simp)) (ih fun a ha => h a (by simp [ha]))

private theorem allowed (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hN : n ≤ 1649375)
    (hz : score n.primeFactorsList % 7 = 0) :
    ∀ p ∈ n.primeFactorsList, p ∈ primes := by
  have oddp {p} (h : p ∈ n.primeFactorsList) : p ≠ 2 := fun e =>
    hodd.not_two_dvd_nat (e ▸ Nat.dvd_of_mem_primeFactorsList h)
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactorsList hp
  by_cases h0 : mark p = 0
  · have hm : p ∈ ([3,41] : List ℕ) := by
      by_contra h
      simp only [mark, if_neg h] at h0
      split at h0 <;> contradiction
    simp at hm
    rcases hm with rfl | rfl <;> decide
  · let s := n.primeFactorsList.erase p
    have perm : n.primeFactorsList.Perm (p :: s) := List.perm_cons_erase hp
    have hw : score n.primeFactorsList = mark p + score s := by
      simpa [score] using (perm.map mark).sum_eq
    have hprod : n = p * s.prod := by
      simpa [Nat.prod_primeFactorsList hn.ne'] using perm.prod_eq
    have hs := prod_lower 5 mark s (fun a ha => power_cost a
      (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_erase ha))
      (oddp (List.mem_of_mem_erase ha)))
    change 5 ^ score s ≤ s.prod at hs
    have hge : 7 - mark p ≤ score s := by omega
    have bp : p * 5 ^ (7 - mark p) ≤ 1649375 := calc
      _ ≤ p * s.prod := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) hge).trans hs)
      _ ≤ _ := hprod ▸ hN
    have hpow : 3125 ≤ 5 ^ (7 - mark p) := Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 5 ≤ 7 - mark p by have := mark_le p; omega)
    have hlt : p < 528 := by
      have := (Nat.mul_le_mul_left p hpow).trans bp
      omega
    have tab : ∀ i : Fin 528, i.val.Prime → i.val ≠ 2 →
        i.val * 5 ^ (7 - mark i.val) ≤ 1649375 → i.val ∈ primes := by decide +kernel
    exact tab ⟨p,hlt⟩ hprime (oddp hp) bp

private theorem search_ok (k x w low : ℕ) (s : List ℕ) (hh : explore k x w low = true)
    (hlen : s.length ≤ k) (hmem : ∀ p ∈ s, p ∈ primes)
    (hlo : ∀ p ∈ s, low ≤ p) (hsort : s.Pairwise (· ≤ ·))
    (hfin : w + score s = 0 ∨ w + score s = 7)
    (hcost : ∀ p ∈ s, 5 ^ mark p ≤ p)
    (hN : x * s.prod ≤ 1649375) : neighbors (x*s.prod) (w+score s) = true := by
  induction k generalizing x w low s with
  | zero =>
    have he : s = [] := List.length_eq_zero_iff.1 (by omega)
    simpa [he,score,explore] using hh
  | succ k ih =>
    obtain ⟨hgood,hall⟩ := Bool.and_eq_true_iff.1 hh
    cases s with
    | nil => simpa [score] using hgood
    | cons p ps =>
      have hsubset := hmem p (by simp)
      have hlo' := hlo p (by simp)
      have hpos : 0 < ps.prod := List.prod_pos (fun a ha => by
        have := hmem a (by simp [ha])
        simp [primes] at this
        omega)
      have hN' : (x*p)*ps.prod ≤ 1649375 := by simpa [Nat.mul_assoc] using hN
      have hsmall : x*p ≤ 1649375 := (Nat.le_mul_of_pos_right _ hpos).trans hN'
      have hfin' : w + mark p + score ps = 0 ∨ w + mark p + score ps = 7 := by
        simpa [score,Nat.add_assoc] using hfin
      have hrest := prod_lower 5 mark ps (fun a ha => hcost a (by simp [ha]))
      change 5 ^ score ps ≤ ps.prod at hrest
      have hpass : w+mark p = 0 ∨ (w+mark p ≤ 7 ∧ (x*p)*5^(7-(w+mark p)) ≤ 1649375) := by
        rcases hfin' with h | h
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide)
             (show 7 - (w+mark p) ≤ score ps by omega)).trans hrest)).trans hN'⟩
      have hrec := List.all_eq_true.1 hall p hsubset
      simp only [hlo',hsmall,hpass,and_self,if_true] at hrec
      have hres := ih (x*p) (w+mark p) p ps hrec (by simp at hlen; omega)
        (fun a ha => hmem a (by simp [ha])) (List.pairwise_cons.1 hsort).1
        (List.pairwise_cons.1 hsort).2 hfin' (fun a ha => hcost a (by simp [ha])) hN'
      simpa [score, Nat.mul_assoc, Nat.add_assoc] using hres
set_option maxHeartbeats 200000000 in
set_option maxRecDepth 8192 in
private theorem checked : explore 21 1 0 0 = true := by decide +kernel
private theorem odd_neighbors (n : ℕ) (hn : 0 < n) (ho : Odd n) (hN : n ≤ 1649375)
    (hz : nz n = false) : (n ≤ 1 ∨ nz (n-1) = true) ∧ (1649375 ≤ n ∨ nz (n+1) = true) := by
  have hzero : score n.primeFactorsList % 7 = 0 := by simpa [nz] using hz
  let s := n.primeFactorsList
  have hmem : ∀ p ∈ s, p ∈ primes := allowed n hn ho hN hzero
  have hprod : s.prod = n := Nat.prod_primeFactorsList hn.ne'
  have hcost : ∀ p ∈ s, 5^mark p ≤ p := by
    intro p hp
    exact power_cost p (Nat.prime_of_mem_primeFactorsList hp)
      (fun h => ho.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactorsList hp))
  have ht := prod_lower 5 mark s hcost
  change 5 ^ score s ≤ s.prod at ht
  have hscore : score s < 14 := by
    by_contra! h
    have := (Nat.pow_le_pow_right (by decide : 0 < 5) h).trans (ht.trans (hprod.symm ▸ hN))
    norm_num at this
  have z : score s % 7 = 0 := hzero
  have hfin : 0 + score s = 0 ∨ 0 + score s = 7 := by omega
  have hl : s.length ≤ 21 := by
    have hh := prod_lower 2 (fun _ => 1) s (fun p hp => by
      simpa using (Nat.prime_of_mem_primeFactorsList hp).two_le)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hh
    by_contra! h
    have := (Nat.pow_le_pow_right (by decide : 0 < 2) (show 22 ≤ s.length by omega)).trans
      (hh.trans (hprod.symm ▸ hN))
    norm_num at this
  have res := search_ok 21 1 0 0 s checked hl hmem (fun _ _ => Nat.zero_le _)
    (Nat.primeFactorsList_sorted n).pairwise hfin hcost (by simpa [hprod] using hN)
  simpa [neighbors,hprod,z] using res

private theorem nonzero_of_bool (n : ℕ) (h : nz n = true) :
    (∑ q ∈ n.primeFactors, (n.factorization q : ZMod 7) * (mark q : ZMod 7)) ≠ 0 := by
  have eqn : score n.primeFactorsList =
      ∑ q ∈ n.primeFactors, n.factorization q * mark q := by
    simpa [score, nsmul_eq_mul, Nat.primeFactorsList_count_eq] using
      Finset.sum_list_map_count n.primeFactorsList mark
  intro hzero
  have hd : 7 ∣ score n.primeFactorsList := (ZMod.natCast_eq_zero_iff _ _).1 (by
    simpa [eqn] using hzero)
  simpa [nz, Nat.mod_eq_zero_of_dvd hd] using h

theorem consecutive (n : ℕ) (hn : 1 ≤ n) (hN : n < 1649375) :
    nz n = true ∨ nz (n+1) = true := by
  by_contra! h
  have h₁ : nz n = false := by simpa using h.1
  have h₂ : nz (n+1) = false := by simpa using h.2
  by_cases ho : Odd n
  · have hx := (odd_neighbors n hn ho hN.le h₁).2
    simp [h₂, Nat.not_le_of_gt hN] at hx
  · have hx := (odd_neighbors (n+1) (by omega) (Nat.odd_add_one.mpr ho) (by omega) h₂).1
    simp [h₁] at hx
    omega

end Odd436

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_seven_two_R1.H2 := by
  intro n hn hN
  have hcast (p : ℕ) : (Odd436.mark p : ZMod 7) =
      (if p ∈ ([3,41] : List ℕ) then 0 else
      if p ∈ ([79,137,197,233,269,277,463,467,797,1709,2647,2903,15791] : List ℕ) then 2 else 1) := by
    unfold Odd436.mark
    split_ifs <;> norm_num
  rcases Odd436.consecutive n hn hN with h | h
  · exact Or.inl (by simpa only [← hcast] using Odd436.nonzero_of_bool n h)
  · exact Or.inr (by simpa only [← hcast] using Odd436.nonzero_of_bool (n+1) h)

