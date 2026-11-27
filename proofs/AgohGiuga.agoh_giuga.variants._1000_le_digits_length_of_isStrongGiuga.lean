import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Lower bound on the decimal digit length of strong Giuga numbers

We prove that every strong Giuga number has at least 13,000 decimal digits, following
the normal-set framework of Giuga and Borwein–Borwein–Borwein–Girgensohn combined with
a 3-case edge-matching dual certificate verified by kernel reduction.
-/

-- Problem: Agoh-Giuga conjecture —  13000 le digits length of isStrongGiuga
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/AgohGiuga.lean:254 (declaration AgohGiuga.agoh_giuga.variants._13000_le_digits_length_of_isStrongGiuga)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace AgohGiugaSolution

open scoped Nat

/- ### Part 1: Giuga's elementary characterization of strong Giuga numbers -/

private lemma sum_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ (p - 1 ∣ k)) :
    ∑ x : ZMod p, x ^ k = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h
    have h1 : g ^ k = 1 := by
      ext
      simpa [Units.val_pow_eq_pow_val] using h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h1
    exact hk h1
  have hmul : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [Finset.mul_sum]
    have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k := by
      refine Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x) ?_ _ _ (fun _ => rfl)
      exact (Units.mulLeft g).bijective
    simpa [mul_pow] using hbij
  have hsub : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgk_ne)

private lemma sum_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} [Fact p.Prime] (hk0 : 0 < k)
    (hk : p - 1 ∣ k) :
    ∑ x : ZMod p, x ^ k = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ := hk
  have hterm : ∀ x : ZMod p, x ^ ((p - 1) * m) = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · subst hx
      exact zero_pow (Nat.ne_of_gt hk0)
    · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow]
  simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  have hcard : (Finset.univ.filter (fun x : ZMod p => ¬ x = 0)).card = p - 1 := by
    have h1 : Finset.univ.filter (fun x : ZMod p => ¬ x = 0) = Finset.univ.erase (0 : ZMod p) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [hcard, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_Ioo_zmod_eq {a p : ℕ} (ha : 1 < a) (hp : p ∣ a) :
    ((∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) : ℕ) : ZMod p) =
      ((a / p : ℕ) : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (a - 1) := by
  have ha1 : a - 1 ≠ 0 := by omega
  have hIoo : ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) = ∑ i ∈ Finset.range a, i ^ (a - 1) := by
    rw [Finset.range_eq_Ico]
    have hsub : Finset.Ioo 0 a = (Finset.Ico 0 a).erase 0 := by
      ext x
      simp [Finset.mem_Ioo, Finset.mem_erase]
      omega
    rw [hsub]
    have h0 : (0 : ℕ) ∈ Finset.Ico 0 a := by simp; omega
    rw [← Finset.add_sum_erase _ _ h0, zero_pow ha1, zero_add]
  rw [hIoo, Nat.cast_sum]
  obtain ⟨m, hm⟩ := hp
  have hm_eq : a / p = m := by
    by_cases hp0 : p = 0
    · subst hp0; simp at hm; omega
    · rw [hm, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp0)]
  rw [hm_eq]
  have hsum : ∀ n : ℕ,
      ∑ i ∈ Finset.range (p * n), ((i : ℕ) : ZMod p) ^ (a - 1) =
        (n : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (a - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [Nat.cast_add, Nat.cast_mul]
  simpa [hm] using hsum m

private lemma sum_range_zmod_eq_univ (p k : ℕ) [NeZero p] :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = ∑ x : ZMod p, x ^ k := by
  refine Finset.sum_bij (fun r _ => (r : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro r₁ hr₁ r₂ hr₂ h
    rw [Finset.mem_range] at hr₁ hr₂
    have := congr_arg ZMod.val h
    simpa [ZMod.val_natCast_of_lt hr₁, ZMod.val_natCast_of_lt hr₂] using this
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩

private lemma strongGiuga_props {a : ℕ} (ha : AgohGiuga.IsStrongGiuga a) :
    (1 < a) ∧
    (Squarefree a) ∧
    (∀ p ∈ a.primeFactors, p % 2 = 1 ∧ 3 ≤ p) ∧
    (∀ p ∈ a.primeFactors, ∀ q ∈ a.primeFactors, ¬ (p ∣ q - 1)) ∧
    (a + 1 ≤ ∑ p ∈ a.primeFactors, a / p) := by
  obtain ⟨hcomp, hdvd_sum⟩ := ha
  have ha1 : 1 < a := hcomp.1
  have ha_not_prime : ¬ a.Prime := hcomp.2
  have ha0 : a ≠ 0 := by omega
  have h1 : ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) ∧ p ∣ (a / p - 1) := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp_mem
    have : Fact p.Prime := ⟨hp⟩
    have hzero : ((1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hpa.trans hdvd_sum)
    rw [Nat.cast_add, Nat.cast_one, sum_Ioo_zmod_eq ha1 hpa, sum_range_zmod_eq_univ] at hzero
    have hpm1 : (p - 1) ∣ (a - 1) := by
      by_contra hnot
      rw [sum_pow_zmod_eq_zero_of_not_dvd hnot, mul_zero, add_zero] at hzero
      exact one_ne_zero hzero
    refine ⟨hpm1, ?_⟩
    rw [sum_pow_zmod_eq_neg_one_of_dvd (by omega) hpm1] at hzero
    have hap_pos : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
    have hcast : ((a / p - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hap_pos, Nat.cast_one]
      linear_combination -hzero
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hpm1 : ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) := fun p hp => (h1 p hp).1
  have hgiuga : ∀ p ∈ a.primeFactors, p ∣ (a / p - 1) := fun p hp => (h1 p hp).2
  have hsq : Squarefree a := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpa : p ∣ a := (dvd_mul_left p p).trans (by simpa [sq] using hp2)
    have hmem : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpa, ha0⟩
    have hdiv1 : p ∣ a / p - 1 := hgiuga p hmem
    have hdiv2 : p ∣ a / p := by
      obtain ⟨k, hk⟩ := hp2
      have : a / p = p * k := by
        rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      exact ⟨k, this⟩
    have hap_pos : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
    have : p ∣ 1 := by
      have hsub := Nat.dvd_sub hdiv2 hdiv1
      rwa [Nat.sub_sub_self hap_pos] at hsub
    exact hp.not_dvd_one this
  have hprod : ∏ p ∈ a.primeFactors, p = a := Nat.prod_primeFactors_of_squarefree hsq
  have hcard2 : 2 ≤ a.primeFactors.card := by
    by_contra hlt
    have hlt' : a.primeFactors.card < 2 := Nat.lt_of_not_ge hlt
    interval_cases hc : a.primeFactors.card
    · rw [Finset.card_eq_zero] at hc
      rw [hc, Finset.prod_empty] at hprod
      omega
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      have hmem : p ∈ a.primeFactors := by rw [hp]; simp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hmem
      rw [hp, Finset.prod_singleton] at hprod
      exact ha_not_prime (hprod ▸ hprime)
  have hodd_all : ∀ p ∈ a.primeFactors, p % 2 = 1 ∧ 3 ≤ p := by
    have h2not : 2 ∉ a.primeFactors := by
      intro h2
      obtain ⟨p, hp_mem, hp_ne⟩ := Finset.exists_mem_ne (by omega : 1 < a.primeFactors.card) 2
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hp_odd : 2 ∣ p - 1 := by
        rcases hp.eq_two_or_odd with rfl | hodd
        · exact absurd rfl hp_ne
        · omega
      have h2_am1 : 2 ∣ a - 1 := hp_odd.trans (hpm1 p hp_mem)
      have h2_a : 2 ∣ a := Nat.dvd_of_mem_primeFactors h2
      have : 2 ∣ 1 := by
        have := Nat.dvd_sub h2_a h2_am1
        rwa [Nat.sub_sub_self (by omega)] at this
      omega
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_ne2 : p ≠ 2 := fun h => h2not (h ▸ hp_mem)
    rcases hp.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hp_ne2
    · exact ⟨hodd, by have := hp.two_le; omega⟩
  have hnorm : ∀ p ∈ a.primeFactors, ∀ q ∈ a.primeFactors, ¬ (p ∣ q - 1) := by
    intro p hp q hq hpq
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_a : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hp_am1 : p ∣ a - 1 := hpq.trans (hpm1 q hq)
    have : p ∣ 1 := by
      have := Nat.dvd_sub hp_a hp_am1
      rwa [Nat.sub_sub_self (by omega)] at this
    exact hp_prime.not_dvd_one this
  have hsum_ge : a + 1 ≤ ∑ p ∈ a.primeFactors, a / p := by
    have hge2 : 2 ≤ ∑ p ∈ a.primeFactors, a / p := by
      obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < a.primeFactors.card)
      have hpair : ({p₁, p₂} : Finset ℕ) ⊆ a.primeFactors := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have hle := Finset.sum_le_sum_of_subset (f := fun p => a / p) hpair
      rw [Finset.sum_pair hne] at hle
      have hp1_le : 1 ≤ a / p₁ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp₁))
        (Nat.prime_of_mem_primeFactors hp₁).pos
      have hp2_le : 1 ≤ a / p₂ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp₂))
        (Nat.prime_of_mem_primeFactors hp₂).pos
      omega
    set M := (∑ p ∈ a.primeFactors, a / p) - 1
    have hM_pos : 0 < M := by omega
    have hM_dvd : a ∣ M := by
      rw [← hprod, Nat.prod_primeFactors_dvd_iff hM_pos.ne']
      intro q hq
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_of_mem_primeFactors hq, ?_, hM_pos.ne'⟩
      have hsplit : ∑ p ∈ a.primeFactors, a / p = a / q + ∑ p ∈ a.primeFactors.erase q, a / p :=
        (Finset.add_sum_erase _ _ hq).symm
      have haq_pos : 1 ≤ a / q := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq))
        (Nat.prime_of_mem_primeFactors hq).pos
      have hM_eq : M = (a / q - 1) + ∑ p ∈ a.primeFactors.erase q, a / p := by
        dsimp [M]; rw [hsplit]; omega
      rw [hM_eq]
      refine dvd_add (hgiuga q hq) (Finset.dvd_sum fun p hp => ?_)
      have hp_ne : p ≠ q := (Finset.mem_erase.mp hp).1
      have hp_mem : p ∈ a.primeFactors := (Finset.mem_erase.mp hp).2
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hp_ne
      have hpq : p * q ∣ a := hcop.mul_dvd_of_dvd_of_dvd
        (Nat.dvd_of_mem_primeFactors hp_mem) (Nat.dvd_of_mem_primeFactors hq)
      obtain ⟨k, hk⟩ := hpq
      refine ⟨k, ?_⟩
      rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp_prime.pos]
    have ha_le_M : a ≤ M := Nat.le_of_dvd hM_pos hM_dvd
    omega
  exact ⟨ha1, hsq, hodd_all, hnorm, hsum_ge⟩

/- ### Part 2: Verified piecewise-constant logarithm, candidate sieve, Trie, and dual bound -/

private def N_CUT : ℕ := 40000
private def L_CUT : ℕ := 244
private def LAM : ℕ := 9760000 -- 40000 * 244
private def TARGET_L : ℕ := 693280 -- 16 * 43330
private def BUDGET : ℕ := 9066720 -- LAM - TARGET_L

inductive LogTree
  | leaf (c : ℕ) : LogTree
  | branch (t : ℕ) (lt ge : LogTree) : LogTree

def LogTree.eval (n : ℕ) : LogTree → ℕ
  | .leaf c => c
  | .branch t l r =>
    match Nat.ble t n with
    | false => l.eval n
    | true => r.eval n

def LogTree.valid (lo : ℕ) : LogTree → Bool
  | .leaf c => Nat.ble (Nat.pow 2 c) (Nat.pow lo 16)
  | .branch t l r =>
    match Nat.ble lo t with
    | false => false
    | true =>
      match l.valid lo with
      | false => false
      | true => r.valid t

private lemma LogTree.pow_eval_le {lo n : ℕ} {lt : LogTree} (h : lt.valid lo = true) (hlo : lo ≤ n) :
    2 ^ lt.eval n ≤ n ^ 16 := by
  induction lt generalizing lo with
  | leaf c =>
    simp only [valid, Nat.ble_eq] at h
    exact h.trans (Nat.pow_le_pow_left hlo 16)
  | branch t l r ihl ihr =>
    simp only [valid] at h
    cases hlot : Nat.ble lo t with
    | false => simp [hlot] at h
    | true =>
      simp only [hlot] at h
      cases hl : l.valid lo with
      | false => simp [hl] at h
      | true =>
        simp only [hl] at h
        simp only [eval]
        cases htn : Nat.ble t n with
        | false => exact ihl hl hlo
        | true => exact ihr h (Nat.ble_eq.mp htn)

private def chkDiv (n d : ℕ) (k : Bool) : Bool :=
  match Nat.beq (Nat.mod n d) 0 with
  | true => Nat.beq n d
  | false => k

private lemma chkDiv_eq_true_of_prime {p d : ℕ} (hp : p.Prime) (hd : 2 ≤ d) {k : Bool}
    (hk : k = true) : chkDiv p d k = true := by
  unfold chkDiv
  cases h : Nat.beq (Nat.mod p d) 0 with
  | false => exact hk
  | true =>
    have hmod : p % d = 0 := Nat.beq_eq.mp h
    have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
    have heq : p = d := ((hp.eq_one_or_self_of_dvd d hdvd).resolve_left (by omega)).symm
    exact Nat.beq_eq.mpr heq

private def isCandOdd (n : ℕ) : Bool :=
  chkDiv n 3 (chkDiv n 5 (chkDiv n 7 (chkDiv n 11 (chkDiv n 13 (chkDiv n 17 (chkDiv n 19
  (chkDiv n 23 (chkDiv n 29 (chkDiv n 31 (chkDiv n 37 (chkDiv n 41 (chkDiv n 43 (chkDiv n 47
  (chkDiv n 53 (chkDiv n 59 (chkDiv n 61 (chkDiv n 67 (chkDiv n 71 (chkDiv n 73 (chkDiv n 79
  (chkDiv n 83 (chkDiv n 89 (chkDiv n 97 (chkDiv n 101 true))))))))))))))))))))))))

private lemma isCandOdd_of_prime {p : ℕ} (hp : p.Prime) : isCandOdd p = true := by
  unfold isCandOdd
  repeat apply chkDiv_eq_true_of_prime hp (by omega)
  rfl

-- 4-ary MSB-first trie of depth d covering [0, 4^d)
inductive Trie
  | empty : Trie
  | leaf (val : ℕ) : Trie
  | node (c0 c1 c2 c3 : Trie) : Trie

def Trie.WF : ℕ → Trie → Prop
  | _, .empty => True
  | 0, .leaf _ => True
  | d + 1, .node c0 c1 c2 c3 => c0.WF d ∧ c1.WF d ∧ c2.WF d ∧ c3.WF d
  | _, _ => False

def Trie.single : ℕ → ℕ → ℕ → Trie
  | 0, _, v => .leaf v
  | d + 1, k, v =>
    let s := Nat.pow 4 d
    let q := Nat.div k s
    let r := Nat.mod k s
    let sub := Trie.single d r v
    match q with
    | 0 => .node sub .empty .empty .empty
    | 1 => .node .empty sub .empty .empty
    | 2 => .node .empty .empty sub .empty
    | _ => .node .empty .empty .empty sub

def Trie.add : Trie → Trie → Trie
  | .empty, t => t
  | t, .empty => t
  | .leaf a, .leaf b => .leaf (Nat.add a b)
  | .node a0 a1 a2 a3, .node b0 b1 b2 b3 =>
    .node (a0.add b0) (a1.add b1) (a2.add b2) (a3.add b3)
  | t, _ => t

def Trie.lookup : ℕ → ℕ → Trie → ℕ
  | _, _, .empty => 0
  | 0, _, .leaf v => v
  | d + 1, r, .node c0 c1 c2 c3 =>
    let s := Nat.pow 4 d
    let q := Nat.div r s
    let rem := Nat.mod r s
    match q with
    | 0 => c0.lookup d rem
    | 1 => c1.lookup d rem
    | 2 => c2.lookup d rem
    | _ => c3.lookup d rem
  | _, _, _ => 0

private lemma Trie.wf_single (d k v : ℕ) : (Trie.single d k v).WF d := by
  induction d generalizing k with
  | zero => trivial
  | succ d ih =>
    simp only [single]
    cases hq : Nat.div k (Nat.pow 4 d) with
    | zero => exact ⟨ih _, by simp [WF], by simp [WF], by simp [WF]⟩
    | succ q1 =>
      cases q1 with
      | zero => exact ⟨by simp [WF], ih _, by simp [WF], by simp [WF]⟩
      | succ q2 =>
        cases q2 with
        | zero => exact ⟨by simp [WF], by simp [WF], ih _, by simp [WF]⟩
        | succ _ => exact ⟨by simp [WF], by simp [WF], by simp [WF], ih _⟩

private lemma Trie.wf_add {d : ℕ} {t1 t2 : Trie} (h1 : t1.WF d) (h2 : t2.WF d) :
    (t1.add t2).WF d := by
  induction d generalizing t1 t2 with
  | zero =>
    cases t1 <;> cases t2 <;> simp_all [WF, add]
  | succ d ih =>
    cases t1 <;> cases t2 <;> simp_all [WF, add]

private lemma nat_div (a b : ℕ) : Nat.div a b = a / b := rfl
private lemma nat_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
private lemma nat_pow (a b : ℕ) : Nat.pow a b = a ^ b := rfl
private lemma nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
private lemma nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
private lemma nat_mul (a b : ℕ) : Nat.mul a b = a * b := rfl

private lemma Trie.lookup_single {d k r v : ℕ} (hk : k < 4 ^ d) (hr : r < 4 ^ d) :
    (Trie.single d k v).lookup d r = if r = k then v else 0 := by
  induction d generalizing k r with
  | zero =>
    have hk0 : k = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hk0; subst hr0; rfl
  | succ d ih =>
    have hs : 0 < 4 ^ d := by positivity
    have hqk : k / 4 ^ d < 4 := by
      rw [Nat.div_lt_iff_lt_mul hs]; simpa [pow_succ'] using hk
    have hqr : r / 4 ^ d < 4 := by
      rw [Nat.div_lt_iff_lt_mul hs]; simpa [pow_succ'] using hr
    have hrk_iff : r = k ↔ r / 4 ^ d = k / 4 ^ d ∧ r % 4 ^ d = k % 4 ^ d := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨hq, hrem⟩
        have h1 := Nat.div_add_mod r (4 ^ d)
        have h2 := Nat.div_add_mod k (4 ^ d)
        rw [hq, hrem] at h1
        omega
    have hrm : r % 4 ^ d < 4 ^ d := Nat.mod_lt r hs
    have hkm : k % 4 ^ d < 4 ^ d := Nat.mod_lt k hs
    simp only [single, nat_div, nat_mod, nat_pow]
    have hqk0 : 0 ≤ k / 4 ^ d := Nat.zero_le _
    have hqr0 : 0 ≤ r / 4 ^ d := Nat.zero_le _
    rcases (by omega : k / 4 ^ d = 0 ∨ k / 4 ^ d = 1 ∨ k / 4 ^ d = 2 ∨ k / 4 ^ d = 3) with
      hkv | hkv | hkv | hkv <;>
    rcases (by omega : r / 4 ^ d = 0 ∨ r / 4 ^ d = 1 ∨ r / 4 ^ d = 2 ∨ r / 4 ^ d = 3) with
      hrv | hrv | hrv | hrv <;>
    simp [hkv, hrv, lookup, nat_div, nat_mod, ih hkm hrm, hrk_iff]

private lemma Trie.lookup_add {d r : ℕ} {t1 t2 : Trie} (h1 : t1.WF d) (h2 : t2.WF d) :
    (t1.add t2).lookup d r = t1.lookup d r + t2.lookup d r := by
  induction d generalizing r t1 t2 with
  | zero =>
    cases t1 <;> cases t2 <;> simp_all [WF, add, lookup]
  | succ d ih =>
    cases t1 <;> cases t2 <;> simp_all [WF, add, lookup]
    cases Nat.div r (Nat.pow 4 d) with
    | zero => rfl
    | succ q1 =>
      cases q1 with
      | zero => rfl
      | succ q2 =>
        cases q2 with
        | zero => rfl
        | succ _ => rfl

-- Simultaneous trie walk summing step (base + r) (t.lookup d r) over r < 4^d
def sumTrieEmpty (step : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, base => step base 0
  | d + 1, base =>
    match Nat.ble 20000 base with
    | true => 0
    | false =>
      let s := Nat.pow 4 d
      Nat.add (Nat.add (sumTrieEmpty step d base) (sumTrieEmpty step d (Nat.add base s)))
              (Nat.add (sumTrieEmpty step d (Nat.add base (Nat.mul 2 s)))
                       (sumTrieEmpty step d (Nat.add base (Nat.mul 3 s))))

def sumTrie (step : ℕ → ℕ → ℕ) : ℕ → ℕ → Trie → ℕ
  | 0, base, .empty => step base 0
  | 0, base, .leaf cov => step base cov
  | 0, base, _ => step base 0
  | d + 1, base, .empty => sumTrieEmpty step (d + 1) base
  | d + 1, base, .node c0 c1 c2 c3 =>
    match Nat.ble 20000 base with
    | true => 0
    | false =>
      let s := Nat.pow 4 d
      Nat.add (Nat.add (sumTrie step d base c0) (sumTrie step d (Nat.add base s) c1))
              (Nat.add (sumTrie step d (Nat.add base (Nat.mul 2 s)) c2)
                       (sumTrie step d (Nat.add base (Nat.mul 3 s)) c3))
  | d + 1, base, _ => sumTrieEmpty step (d + 1) base

private lemma sum_range_four_mul (f : ℕ → ℕ) (s : ℕ) :
    ∑ r ∈ Finset.range (4 * s), f r =
      (∑ r ∈ Finset.range s, f r + ∑ r ∈ Finset.range s, f (s + r)) +
      (∑ r ∈ Finset.range s, f (2 * s + r) + ∑ r ∈ Finset.range s, f (3 * s + r)) := by
  have h4 : 4 * s = (s + s) + (s + s) := by omega
  rw [h4, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_range_add f s s
  · rw [Finset.sum_range_add]
    congr 1 <;> refine Finset.sum_congr rfl fun r _ => ?_ <;> congr 1 <;> omega

private lemma sumTrieEmpty_eq (step : ℕ → ℕ → ℕ)
    (hzero : ∀ k cov, 20000 ≤ k → step k cov = 0)
    (d base : ℕ) :
    sumTrieEmpty step d base = ∑ r ∈ Finset.range (4 ^ d), step (base + r) 0 := by
  induction d generalizing base with
  | zero => simp [sumTrieEmpty]
  | succ d ih =>
    simp only [sumTrieEmpty]
    cases hb : Nat.ble 20000 base with
    | true =>
      have hge : 20000 ≤ base := Nat.ble_eq.mp hb
      symm
      exact Finset.sum_eq_zero fun r _ => hzero _ _ (by omega)
    | false =>
      have hpow : 4 ^ (d + 1) = 4 * 4 ^ d := by rw [pow_succ']
      rw [hpow, sum_range_four_mul]
      simp only [nat_add, nat_mul, nat_pow, ih]
      congr 1 <;> congr 1 <;> refine Finset.sum_congr rfl fun r _ => ?_ <;>
        congr 1 <;> omega

private lemma sumTrie_eq (step : ℕ → ℕ → ℕ)
    (hzero : ∀ k cov, 20000 ≤ k → step k cov = 0)
    (d base : ℕ) (t : Trie) (ht : t.WF d) :
    sumTrie step d base t =
      ∑ r ∈ Finset.range (4 ^ d), step (base + r) (t.lookup d r) := by
  induction d generalizing base t with
  | zero =>
    cases t with
    | empty => simp [sumTrie, Trie.lookup]
    | leaf v => simp [sumTrie, Trie.lookup]
    | node => exact False.elim ht
  | succ d ih =>
    cases t with
    | empty =>
      simp only [sumTrie, Trie.lookup]
      exact sumTrieEmpty_eq step hzero (d + 1) base
    | leaf _ => exact False.elim ht
    | node c0 c1 c2 c3 =>
      simp only [sumTrie]
      cases hb : Nat.ble 20000 base with
      | true =>
        have hge : 20000 ≤ base := Nat.ble_eq.mp hb
        symm
        exact Finset.sum_eq_zero fun r _ => hzero _ _ (by omega)
      | false =>
        have hpow : 4 ^ (d + 1) = 4 * 4 ^ d := by rw [pow_succ']
        rw [hpow, sum_range_four_mul]
        simp only [nat_add, nat_mul, nat_pow]
        rw [ih base c0 ht.1, ih (base + 4 ^ d) c1 ht.2.1,
            ih (base + 2 * 4 ^ d) c2 ht.2.2.1, ih (base + 3 * 4 ^ d) c3 ht.2.2.2]
        have hs : 0 < 4 ^ d := by positivity
        have h0 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) r (.node c0 c1 c2 c3) = c0.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          simp [Trie.lookup, nat_div, nat_mod, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
        have h1 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) (4 ^ d + r) (.node c0 c1 c2 c3) = c1.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hd1 : (4 ^ d + r) / 4 ^ d = 1 := by
            rw [Nat.add_div_left r hs, Nat.div_eq_of_lt hr]
          have hm1 : (4 ^ d + r) % 4 ^ d = r := by
            rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
          simp [Trie.lookup, nat_div, nat_mod, hd1, hm1]
        have h2 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) (2 * 4 ^ d + r) (.node c0 c1 c2 c3) = c2.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hd2 : (2 * 4 ^ d + r) / 4 ^ d = 2 := by
            rw [mul_comm 2, Nat.mul_add_div hs, Nat.div_eq_of_lt hr]
          have hm2 : (2 * 4 ^ d + r) % 4 ^ d = r := by
            rw [mul_comm 2, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
          simp [Trie.lookup, nat_div, nat_mod, hd2, hm2]
        have h3 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) (3 * 4 ^ d + r) (.node c0 c1 c2 c3) = c3.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hd3 : (3 * 4 ^ d + r) / 4 ^ d = 3 := by
            rw [mul_comm 3, Nat.mul_add_div hs, Nat.div_eq_of_lt hr]
          have hm3 : (3 * 4 ^ d + r) % 4 ^ d = r := by
            rw [mul_comm 3, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
          simp [Trie.lookup, nat_div, nat_mod, hd3, hm3]
        congr 1
        · congr 1
          · refine Finset.sum_congr rfl fun r hr => by rw [h0 r hr]
          · refine Finset.sum_congr rfl fun r hr => by rw [h1 r hr, add_assoc]
        · congr 1
          · refine Finset.sum_congr rfl fun r hr => by rw [h2 r hr, add_assoc]
          · refine Finset.sum_congr rfl fun r hr => by rw [h3 r hr, add_assoc]

-- Balanced binary tree of dual matching edges (u, v, c)
inductive ET
  | e (u v c : ℕ) : ET
  | n (l r : ET) : ET

def ET.toTrie : ET → Trie
  | .e u v c => (Trie.single 8 (Nat.div (Nat.sub u 1) 2) c).add
                (Trie.single 8 (Nat.div (Nat.sub v 1) 2) c)
  | .n l r => l.toTrie.add r.toTrie

def ET.valid : ET → Bool
  | .e u v _ =>
    match Nat.ble 3 u with
    | false => false
    | true =>
      match Nat.ble (Nat.add u 1) v with
      | false => false
      | true =>
        match Nat.ble v 39999 with
        | false => false
        | true =>
          match Nat.beq (Nat.mod u 2) 1 with
          | false => false
          | true =>
            match Nat.beq (Nat.mod v 2) 1 with
            | false => false
            | true => Nat.beq (Nat.mod (Nat.sub v 1) u) 0
  | .n l r =>
    match l.valid with
    | false => false
    | true => r.valid

def ET.sumC : ET → ℕ
  | .e _ _ c => c
  | .n l r => Nat.add l.sumC r.sumC

private lemma ET.wf_toTrie (et : ET) : et.toTrie.WF 8 := by
  induction et with
  | e u v c => exact Trie.wf_add (Trie.wf_single _ _ _) (Trie.wf_single _ _ _)
  | n l r ihl ihr => exact Trie.wf_add ihl ihr

private lemma ET.sum_lookup_le (S : Finset ℕ)
    (hodd : ∀ p ∈ S, p % 2 = 1)
    (hnorm : ∀ p ∈ S, ∀ q ∈ S, ¬ (p ∣ q - 1))
    (hlt : ∀ p ∈ S, p < 40000)
    (et : ET) (hv : et.valid = true) :
    ∑ p ∈ S, et.toTrie.lookup 8 ((p - 1) / 2) ≤ et.sumC := by
  induction et with
  | e u v c =>
    simp only [valid] at hv
    -- Extract all 6 conditions from hv
    have hu3 : 3 ≤ u := by
      cases h : Nat.ble 3 u <;> simp [h] at hv; exact Nat.ble_eq.mp h
    have huv : u + 1 ≤ v := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      simp only [h1] at hv
      cases h : Nat.ble (Nat.add u 1) v <;> simp [h] at hv; exact Nat.ble_eq.mp h
    have hvN : v ≤ 39999 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      simp only [h1, h2] at hv
      cases h : Nat.ble v 39999 <;> simp [h] at hv; exact Nat.ble_eq.mp h
    have huodd : u % 2 = 1 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      have h3 : Nat.ble v 39999 = true := Nat.ble_eq.mpr hvN
      simp only [h1, h2, h3] at hv
      cases h : Nat.beq (Nat.mod u 2) 1 <;> simp [h] at hv; exact Nat.beq_eq.mp h
    have hvodd : v % 2 = 1 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      have h3 : Nat.ble v 39999 = true := Nat.ble_eq.mpr hvN
      have h4 : Nat.beq (Nat.mod u 2) 1 = true := Nat.beq_eq.mpr huodd
      simp only [h1, h2, h3, h4] at hv
      cases h : Nat.beq (Nat.mod v 2) 1 <;> simp [h] at hv; exact Nat.beq_eq.mp h
    have hdvd : u ∣ v - 1 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      have h3 : Nat.ble v 39999 = true := Nat.ble_eq.mpr hvN
      have h4 : Nat.beq (Nat.mod u 2) 1 = true := Nat.beq_eq.mpr huodd
      have h5 : Nat.beq (Nat.mod v 2) 1 = true := Nat.beq_eq.mpr hvodd
      simp only [h1, h2, h3, h4, h5] at hv
      exact Nat.dvd_of_mod_eq_zero (Nat.beq_eq.mp hv)
    have hterm : ∀ p ∈ S,
        (ET.e u v c).toTrie.lookup 8 ((p - 1) / 2) =
          (if p = u then c else 0) + (if p = v then c else 0) := by
      intro p hp
      have hpodd := hodd p hp
      have hplt := hlt p hp
      simp only [toTrie, nat_sub, nat_div]
      rw [Trie.lookup_add (Trie.wf_single _ _ _) (Trie.wf_single _ _ _),
          Trie.lookup_single (by omega) (by omega),
          Trie.lookup_single (by omega) (by omega)]
      have hequ : (p - 1) / 2 = (u - 1) / 2 ↔ p = u := by omega
      have heqv : (p - 1) / 2 = (v - 1) / 2 ↔ p = v := by omega
      simp [hequ, heqv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [sumC]
    by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
    · exact absurd hdvd (hnorm u huS v hvS)
    · simp [huS, hvS]
    · simp [huS, hvS]
    · simp [huS, hvS]
  | n l r ihl ihr =>
    simp only [valid] at hv
    cases hl : l.valid with
    | false => simp [hl] at hv
    | true =>
      simp only [hl] at hv
      have hterm : ∀ p ∈ S,
          (ET.n l r).toTrie.lookup 8 ((p - 1) / 2) =
            l.toTrie.lookup 8 ((p - 1) / 2) + r.toTrie.lookup 8 ((p - 1) / 2) := by
        intro p _
        exact Trie.lookup_add l.wf_toTrie r.wf_toTrie
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      simp only [sumC, nat_add]
      exact Nat.add_le_add (ihl hl) (ihr hv)


/- ### Part 3: Concrete LogTree, weight reduction, and 3-case certificates -/

private def myLogTree : LogTree :=
  LogTree.branch 40000 (LogTree.branch 8934 (LogTree.branch 2897 (LogTree.branch 470 (LogTree.branch 40 (LogTree.branch 8 (LogTree.branch 3 (LogTree.leaf 0) (LogTree.leaf 25)) (LogTree.branch 17 (LogTree.leaf 45) (LogTree.leaf 65))) (LogTree.branch 182 (LogTree.branch 95 (LogTree.leaf 85) (LogTree.leaf 105)) (LogTree.branch 305 (LogTree.leaf 120) (LogTree.leaf 132)))) (LogTree.branch 1387 (LogTree.branch 862 (LogTree.branch 664 (LogTree.leaf 142) (LogTree.leaf 150)) (LogTree.branch 1117 (LogTree.leaf 156) (LogTree.leaf 162))) (LogTree.branch 2048 (LogTree.branch 1723 (LogTree.leaf 167) (LogTree.leaf 172)) (LogTree.branch 2436 (LogTree.leaf 176) (LogTree.leaf 180))))) (LogTree.branch 6317 (LogTree.branch 4871 (LogTree.branch 3757 (LogTree.branch 3299 (LogTree.leaf 184) (LogTree.leaf 187)) (LogTree.branch 4278 (LogTree.leaf 190) (LogTree.leaf 193))) (LogTree.branch 5793 (LogTree.branch 5548 (LogTree.leaf 196) (LogTree.leaf 199)) (LogTree.branch 6050 (LogTree.leaf 200) (LogTree.leaf 201)))) (LogTree.branch 7513 (LogTree.branch 6889 (LogTree.branch 6597 (LogTree.leaf 202) (LogTree.leaf 203)) (LogTree.branch 7194 (LogTree.leaf 204) (LogTree.leaf 205))) (LogTree.branch 8192 (LogTree.branch 7845 (LogTree.leaf 206) (LogTree.leaf 207)) (LogTree.branch 8555 (LogTree.leaf 208) (LogTree.leaf 209)))))) (LogTree.branch 17867 (LogTree.branch 12634 (LogTree.branch 10624 (LogTree.branch 9742 (LogTree.branch 9329 (LogTree.leaf 210) (LogTree.leaf 211)) (LogTree.branch 10174 (LogTree.leaf 212) (LogTree.leaf 213))) (LogTree.branch 11586 (LogTree.branch 11095 (LogTree.leaf 214) (LogTree.leaf 215)) (LogTree.branch 12099 (LogTree.leaf 216) (LogTree.leaf 217)))) (LogTree.branch 15025 (LogTree.branch 13778 (LogTree.branch 13194 (LogTree.leaf 218) (LogTree.leaf 219)) (LogTree.branch 14388 (LogTree.leaf 220) (LogTree.leaf 221))) (LogTree.branch 16384 (LogTree.branch 15690 (LogTree.leaf 222) (LogTree.leaf 223)) (LogTree.branch 17110 (LogTree.leaf 224) (LogTree.leaf 225))))) (LogTree.branch 25268 (LogTree.branch 21248 (LogTree.branch 19484 (LogTree.branch 18658 (LogTree.leaf 226) (LogTree.leaf 227)) (LogTree.branch 20347 (LogTree.leaf 228) (LogTree.leaf 229))) (LogTree.branch 23171 (LogTree.branch 22189 (LogTree.leaf 230) (LogTree.leaf 231)) (LogTree.branch 24197 (LogTree.leaf 232) (LogTree.leaf 233)))) (LogTree.branch 30049 (LogTree.branch 27555 (LogTree.branch 26387 (LogTree.leaf 234) (LogTree.leaf 235)) (LogTree.branch 28775 (LogTree.leaf 236) (LogTree.leaf 237))) (LogTree.branch 32768 (LogTree.branch 31379 (LogTree.leaf 238) (LogTree.leaf 239)) (LogTree.branch 34219 (LogTree.leaf 240) (LogTree.branch 35734 (LogTree.leaf 241) (LogTree.leaf 242)))))))) (LogTree.leaf 244)

private lemma myLogTree_valid : myLogTree.valid 1 = true := by rfl

private lemma two_pow_eval_le (p : ℕ) (hp : 1 ≤ p) : 2 ^ myLogTree.eval p ≤ p ^ 16 :=
  LogTree.pow_eval_le myLogTree_valid hp

private def weightOf (n : ℕ) : ℕ :=
  Nat.sub (Nat.div (Nat.add LAM (Nat.sub n 1)) n) (myLogTree.eval n)

private lemma weightOf_eq_zero_of_ge {p : ℕ} (hp : 40000 ≤ p) : weightOf p = 0 := by
  have hev : myLogTree.eval p = 244 := by
    simp only [myLogTree, LogTree.eval, Nat.ble_eq.mpr hp]
  unfold weightOf
  rw [hev, nat_sub, nat_div, nat_add, nat_sub]
  have hdiv : (LAM + (p - 1)) / p ≤ 244 := by
    have hlt : LAM + (p - 1) < p * 245 := by
      dsimp [LAM]
      omega
    have h1 : (LAM + (p - 1)) / p < 245 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  omega

private lemma lam_le_mul_eval_add_weight {p : ℕ} (hp : 1 ≤ p) :
    LAM ≤ p * (myLogTree.eval p + weightOf p) := by
  have hceil : LAM ≤ p * ((LAM + (p - 1)) / p) := by
    have hmod := Nat.div_add_mod (LAM + (p - 1)) p
    have hlt := Nat.mod_lt (LAM + (p - 1)) (by omega : 0 < p)
    omega
  have hw : (LAM + (p - 1)) / p ≤ myLogTree.eval p + weightOf p := by
    unfold weightOf
    rw [nat_sub, nat_div, nat_add, nat_sub]
    omega
  exact hceil.trans (Nat.mul_le_mul_left p hw)

private lemma digits_ge_13000_of_weight_bound {a : ℕ}
    (ha : AgohGiuga.IsStrongGiuga a)
    (hw : ∑ p ∈ a.primeFactors.filter (· < 40000), weightOf p ≤ BUDGET) :
    13000 ≤ (Nat.digits 10 a).length := by
  obtain ⟨ha1, hsq, hodd, _, hsum_ge⟩ := strongGiuga_props ha
  set S := a.primeFactors
  have hprod : ∏ p ∈ S, p = a := Nat.prod_primeFactors_of_squarefree hsq
  have hw_all : ∑ p ∈ S, weightOf p ≤ BUDGET := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not S (· < 40000) weightOf).symm
    have hzero : ∑ p ∈ S.filter (fun x => ¬ x < 40000), weightOf p = 0 :=
      Finset.sum_eq_zero fun p hp => weightOf_eq_zero_of_ge (by
        have := (Finset.mem_filter.mp hp).2; omega)
    rw [hsplit, hzero, add_zero]
    exact hw
  have hterm : ∀ p ∈ S, LAM * (a / p) ≤ a * (myLogTree.eval p + weightOf p) := by
    intro p hp
    have hp3 : 3 ≤ p := (hodd p hp).2
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hmul : p * (a / p) = a := Nat.mul_div_cancel' hpa
    calc
      LAM * (a / p) ≤ (p * (myLogTree.eval p + weightOf p)) * (a / p) :=
        Nat.mul_le_mul_right _ (lam_le_mul_eval_add_weight (by omega))
      _ = (p * (a / p)) * (myLogTree.eval p + weightOf p) := by ring
      _ = a * (myLogTree.eval p + weightOf p) := by rw [hmul]
  have hsum_ineq : LAM * (a + 1) ≤ a * (∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p) := by
    calc
      LAM * (a + 1) ≤ LAM * ∑ p ∈ S, a / p := Nat.mul_le_mul_left _ hsum_ge
      _ = ∑ p ∈ S, LAM * (a / p) := Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ S, a * (myLogTree.eval p + weightOf p) := Finset.sum_le_sum hterm
      _ = a * ∑ p ∈ S, (myLogTree.eval p + weightOf p) := (Finset.mul_sum _ _ _).symm
      _ = a * (∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p) := by rw [Finset.sum_add_distrib]
  have hlam_lt : LAM < ∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p := by
    have h1 : a * LAM < a * (∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p) := by
      have : LAM * (a + 1) = a * LAM + LAM := by ring
      have : 0 < LAM := by decide
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have hL_ge : TARGET_L ≤ ∑ p ∈ S, myLogTree.eval p := by
    have : LAM - BUDGET = TARGET_L := by decide
    omega
  have hpow2 : 2 ^ TARGET_L ≤ a ^ 16 := by
    calc
      2 ^ TARGET_L ≤ 2 ^ (∑ p ∈ S, myLogTree.eval p) := Nat.pow_le_pow_right (by norm_num) hL_ge
      _ = ∏ p ∈ S, 2 ^ myLogTree.eval p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ p ∈ S, p ^ 16 := Finset.prod_le_prod' fun p hp =>
        two_pow_eval_le p (by have := (hodd p hp).2; omega)
      _ = (∏ p ∈ S, p) ^ 16 := Finset.prod_pow S 16 (fun p => p)
      _ = a ^ 16 := by rw [hprod]
  have h10 : (10 ^ 12999) ^ 16 ≤ 2 ^ TARGET_L := by
    have hstep : 10 ^ 12999 ≤ 2 ^ 43330 := by
      have h1 : 10 ^ 12999 = (10 ^ 3) ^ 4333 := by
        have : 12999 = 3 * 4333 := by norm_num
        rw [this, pow_mul]
      have h2 : (2 ^ 10) ^ 4333 = 2 ^ 43330 := by
        have : 43330 = 10 * 4333 := by norm_num
        rw [this, pow_mul]
      rw [h1, ← h2]
      exact Nat.pow_le_pow_left (by norm_num) 4333
    have h3 : (2 ^ 43330) ^ 16 = 2 ^ TARGET_L := by
      have : TARGET_L = 43330 * 16 := by decide
      rw [this, pow_mul]
    rw [← h3]
    exact Nat.pow_le_pow_left hstep 16
  have ha_ge : 10 ^ 12999 ≤ a :=
    (Nat.pow_le_pow_iff_left (by norm_num : 16 ≠ 0)).mp (h10.trans hpow2)
  have hlt_dig : 12999 < (Nat.digits 10 a).length :=
    (Nat.lt_digits_length_iff (by norm_num : 1 < 10) a).mpr ha_ge
  omega

private def stepCase (filt : ℕ → Bool) (k cov : ℕ) : ℕ :=
  match Nat.ble 20000 k with
  | true => 0
  | false =>
    match Nat.beq k 0 with
    | true => 0
    | false =>
      let n := Nat.add (Nat.mul 2 k) 1
      match filt n with
      | false => 0
      | true =>
        match isCandOdd n with
        | false => 0
        | true => Nat.sub (weightOf n) cov

private lemma stepCase_zero_ge (filt : ℕ → Bool) (k cov : ℕ) (hk : 20000 ≤ k) :
    stepCase filt k cov = 0 := by
  simp only [stepCase, Nat.ble_eq.mpr hk]

private lemma sum_weight_filter_le (S : Finset ℕ) (filt : ℕ → Bool) (et : ET)
    (hprime : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, p % 2 = 1 ∧ 3 ≤ p)
    (hnorm : ∀ p ∈ S, ∀ q ∈ S, ¬ (p ∣ q - 1))
    (hlt : ∀ p ∈ S, p < 40000)
    (hfilt : ∀ p ∈ S, filt p = true)
    (hv : et.valid = true) :
    ∑ p ∈ S, weightOf p ≤ et.sumC + sumTrie (stepCase filt) 8 0 et.toTrie := by
  have hpoint : ∀ p ∈ S,
      weightOf p ≤ et.toTrie.lookup 8 ((p - 1) / 2) +
        stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) := by
    intro p hp
    have hpo := hodd p hp
    have hplt := hlt p hp
    have hk_lt : (p - 1) / 2 < 20000 := by omega
    have hk_ne0 : (p - 1) / 2 ≠ 0 := by omega
    have hble : Nat.ble 20000 ((p - 1) / 2) = false := by
      cases h : Nat.ble 20000 ((p - 1) / 2) with
      | false => rfl
      | true => have := Nat.ble_eq.mp h; omega
    have hbeq : Nat.beq ((p - 1) / 2) 0 = false := by
      cases h : Nat.beq ((p - 1) / 2) 0 with
      | false => rfl
      | true => exact absurd (Nat.beq_eq.mp h) hk_ne0
    have hn_eq : Nat.add (Nat.mul 2 ((p - 1) / 2)) 1 = p := by
      rw [nat_add, nat_mul]; omega
    have hstep : stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) =
        weightOf p - et.toTrie.lookup 8 ((p - 1) / 2) := by
      unfold stepCase
      rw [hble, hbeq]
      dsimp only
      rw [hn_eq, hfilt p hp, isCandOdd_of_prime (hprime p hp), nat_sub]
    rw [hstep]
    omega
  have h1 : ∑ p ∈ S, weightOf p ≤
      ∑ p ∈ S, et.toTrie.lookup 8 ((p - 1) / 2) +
      ∑ p ∈ S, stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpoint
  have h2 : ∑ p ∈ S, et.toTrie.lookup 8 ((p - 1) / 2) ≤ et.sumC :=
    et.sum_lookup_le S (fun p hp => (hodd p hp).1) hnorm hlt hv
  have h3 : ∑ p ∈ S, stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) ≤
      sumTrie (stepCase filt) 8 0 et.toTrie := by
    rw [sumTrie_eq (stepCase filt) (stepCase_zero_ge filt) 8 0 et.toTrie et.wf_toTrie]
    have hinj : Set.InjOn (fun p => (p - 1) / 2) (S : Set ℕ) := by
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only at heq
      have h1 := (hodd p₁ hp₁).1
      have h2 := (hodd p₂ hp₂).1
      omega
    have himg : S.image (fun p => (p - 1) / 2) ⊆ Finset.range (4 ^ 8) := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      have := hlt p hp
      rw [Finset.mem_range]
      omega
    calc
      ∑ p ∈ S, stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2))
          = ∑ r ∈ S.image (fun p => (p - 1) / 2), stepCase filt r (et.toTrie.lookup 8 r) :=
        (Finset.sum_image (f := fun r => stepCase filt r (et.toTrie.lookup 8 r))
          (fun p₁ hp₁ p₂ hp₂ h => hinj hp₁ hp₂ h)).symm
      _ ≤ ∑ r ∈ Finset.range (4 ^ 8), stepCase filt r (et.toTrie.lookup 8 r) :=
        Finset.sum_le_sum_of_subset himg
      _ = ∑ r ∈ Finset.range (4 ^ 8), stepCase filt (0 + r) (et.toTrie.lookup 8 r) := by
        simp_rw [zero_add]
  exact h1.trans (Nat.add_le_add h2 h3)

private def filt1 (n : ℕ) : Bool :=
  Nat.beq (Nat.mod n 3) 2

private def filt2 (n : ℕ) : Bool :=
  match Nat.beq n 3 with
  | true => false
  | false =>
    match Nat.beq n 5 with
    | true => false
    | false =>
      match Nat.beq (Nat.mod n 5) 1 with
      | true => false
      | false => true

private def filt3 (n : ℕ) : Bool :=
  match Nat.beq n 3 with
  | true => false
  | false =>
    match Nat.beq n 5 with
    | true => false
    | false => true

private def etCase1_0 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 5 11 887228) (ET.e 17 137 71136)) (ET.n (ET.e 5 281 34614) (ET.e 5 521 18592))) (ET.n (ET.n (ET.e 5 761 12676) (ET.e 5 971 9896)) (ET.n (ET.e 83 1163 8231) (ET.n (ET.e 653 1307 7306) (ET.e 5 1571 6046))))) (ET.n (ET.n (ET.n (ET.e 5 1871 5045) (ET.e 5 2111 4448)) (ET.n (ET.e 173 2423 3853) (ET.e 17 2687 3453))) (ET.n (ET.n (ET.e 113 2939 3137) (ET.e 23 3359 2719)) (ET.n (ET.e 479 3833 2357) (ET.n (ET.e 2039 4079 2203) (ET.e 89 4451 2000)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2399 4799 1841) (ET.e 83 5147 1701)) (ET.n (ET.e 2699 5399 1612) (ET.e 23 5843 1471))) (ET.n (ET.n (ET.e 83 6143 1388) (ET.e 3329 6659 1263)) (ET.n (ET.e 3491 6983 1194) (ET.n (ET.e 149 7451 1105) (ET.e 3803 7607 1078))))) (ET.n (ET.n (ET.n (ET.e 29 8237 977) (ET.e 197 8669 917)) (ET.n (ET.e 4481 8963 879) (ET.n (ET.e 467 9341 834) (ET.e 17 9623 804)))) (ET.n (ET.n (ET.e 1229 9833 781) (ET.e 17 10133 752)) (ET.n (ET.e 5231 10463 720) (ET.n (ET.e 5501 11003 674) (ET.e 29 11369 644))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 11663 621) (ET.e 17 12071 593)) (ET.n (ET.e 6173 12347 574) (ET.e 293 12893 539))) (ET.n (ET.n (ET.e 947 13259 518) (ET.e 977 13679 495)) (ET.n (ET.e 29 14153 470) (ET.n (ET.e 17 14621 447) (ET.e 23 14951 432))))) (ET.n (ET.n (ET.n (ET.e 479 15329 415) (ET.e 7823 15647 402)) (ET.n (ET.e 29 16067 385) (ET.n (ET.e 17 16253 378) (ET.e 197 16943 353)))) (ET.n (ET.n (ET.e 1223 17123 345) (ET.e 2207 17657 328)) (ET.n (ET.e 29 17981 317) (ET.n (ET.e 53 18233 310) (ET.e 83 18593 299)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 9473 18947 289) (ET.e 263 19463 275)) (ET.n (ET.e 1433 20063 259) (ET.e 10271 20543 247))) (ET.n (ET.n (ET.e 2609 20873 239) (ET.e 173 21107 234)) (ET.n (ET.e 10733 21467 225) (ET.n (ET.e 10883 21767 219) (ET.e 29 22157 211))))) (ET.n (ET.n (ET.n (ET.e 2801 22409 205) (ET.e 2837 22697 200)) (ET.n (ET.e 17 23087 192) (ET.n (ET.e 17 23393 186) (ET.e 11813 23627 182)))) (ET.n (ET.n (ET.e 29 24071 174) (ET.e 23 24473 166)) (ET.n (ET.e 23 24749 162) (ET.n (ET.e 23 25163 155) (ET.e 23 25439 150)))))))
private def etCase1_1 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 5 41 237964) (ET.e 83 167 58339)) (ET.n (ET.e 5 311 31251) (ET.e 293 587 16485))) (ET.n (ET.n (ET.e 5 821 11738) (ET.e 23 1013 9479)) (ET.n (ET.e 5 1181 8103) (ET.n (ET.e 659 1319 7238) (ET.e 113 1583 5999))))) (ET.n (ET.n (ET.n (ET.e 5 1901 4963) (ET.e 5 2141 4383)) (ET.n (ET.e 5 2441 3819) (ET.e 5 2711 3421))) (ET.n (ET.n (ET.e 53 2969 3104) (ET.e 173 3461 2633)) (ET.n (ET.e 17 3911 2306) (ET.n (ET.e 2063 4127 2175) (ET.e 557 4457 1997)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 23 4877 1806) (ET.e 23 5153 1699)) (ET.n (ET.e 677 5417 1606) (ET.e 17 5849 1469))) (ET.n (ET.n (ET.e 17 6257 1359) (ET.e 3389 6779 1237)) (ET.n (ET.e 29 7019 1187) (ET.n (ET.e 17 7481 1100) (ET.e 3821 7643 1071))))) (ET.n (ET.n (ET.n (ET.e 317 8243 977) (ET.e 53 8693 914)) (ET.n (ET.e 17 9011 874) (ET.n (ET.e 293 9377 830) (ET.e 29 9629 803)))) (ET.n (ET.n (ET.e 4919 9839 780) (ET.e 29 10151 750)) (ET.n (ET.e 29 10499 717) (ET.n (ET.e 29 11021 672) (ET.e 89 11393 642))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 29 11717 617) (ET.e 83 12119 589)) (ET.n (ET.e 17 12377 572) (ET.e 6449 12899 539))) (ET.n (ET.n (ET.e 17 13397 510) (ET.e 23 13709 493)) (ET.n (ET.e 7079 14159 470) (ET.n (ET.e 563 14639 446) (ET.e 1877 15017 429))))) (ET.n (ET.n (ET.n (ET.e 7673 15347 414) (ET.e 7841 15683 401)) (ET.n (ET.e 503 16097 384) (ET.n (ET.e 8273 16547 366) (ET.e 653 16979 351)))) (ET.n (ET.n (ET.e 23 17159 344) (ET.e 17 17681 328)) (ET.n (ET.e 17 17987 317) (ET.n (ET.e 29 18329 307) (ET.e 17 18701 295)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 173 19031 286) (ET.e 977 19541 272)) (ET.n (ET.e 17 20129 257) (ET.e 467 20549 246))) (ET.n (ET.n (ET.e 653 20897 239) (ET.e 17 21149 233)) (ET.n (ET.e 827 21503 224) (ET.n (ET.e 29 21809 218) (ET.e 359 22259 208))))) (ET.n (ET.n (ET.n (ET.e 11243 22487 204) (ET.e 23 22817 197)) (ET.n (ET.e 11549 23099 192) (ET.n (ET.e 11699 23399 186) (ET.e 11831 23663 181)))) (ET.n (ET.n (ET.e 12041 24083 174) (ET.e 12251 24503 166)) (ET.n (ET.e 29 24767 162) (ET.n (ET.e 293 25199 155) (ET.e 29 25463 150)))))))
private def etCase1_2 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 23 47 207575) (ET.e 89 179 54421)) (ET.n (ET.e 173 347 27995) (ET.e 23 599 16152))) (ET.n (ET.n (ET.e 419 839 11483) (ET.e 509 1019 9423)) (ET.n (ET.e 593 1187 8061) (ET.n (ET.e 5 1361 7010) (ET.e 5 1601 5930))))) (ET.n (ET.n (ET.n (ET.e 5 1931 4883) (ET.e 269 2153 4358)) (ET.n (ET.e 1223 2447 3809) (ET.e 5 2741 3381))) (ET.n (ET.n (ET.e 1499 2999 3071) (ET.e 1733 3467 2629)) (ET.n (ET.e 89 3917 2302) (ET.n (ET.e 2069 4139 2169) (ET.e 23 4463 1994)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 4931 1784) (ET.e 17 5237 1668)) (ET.n (ET.e 17 5441 1598) (ET.e 293 5861 1466))) (ET.n (ET.n (ET.e 449 6287 1352) (ET.e 3413 6827 1227)) (ET.n (ET.e 503 7043 1182) (ET.n (ET.e 197 7487 1099) (ET.e 3851 7703 1062))))) (ET.n (ET.n (ET.n (ET.e 17 8297 969) (ET.e 4349 8699 913)) (ET.n (ET.e 113 9041 870) (ET.n (ET.e 17 9419 826) (ET.e 173 9689 797)))) (ET.n (ET.n (ET.e 197 9851 779) (ET.e 5081 10163 749)) (ET.n (ET.e 53 10601 708) (ET.n (ET.e 149 11027 672) (ET.e 5711 11423 640))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 23 11777 613) (ET.e 467 12143 587)) (ET.n (ET.e 29 12413 570) (ET.e 6491 12983 534))) (ET.n (ET.n (ET.e 269 13451 507) (ET.e 983 13763 491)) (ET.n (ET.e 7151 14303 463) (ET.n (ET.e 7349 14699 443) (ET.e 53 15053 427))))) (ET.n (ET.n (ET.n (ET.e 1097 15359 414) (ET.e 7853 15707 399)) (ET.n (ET.e 83 16103 384) (ET.e 2069 16553 366))) (ET.n (ET.n (ET.e 23 17021 350) (ET.e 1229 17207 343)) (ET.n (ET.e 887 17741 326) (ET.n (ET.e 9029 18059 315) (ET.e 23 18401 305)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2339 18713 295) (ET.e 149 19073 285)) (ET.n (ET.e 983 19661 269) (ET.e 1439 20147 257))) (ET.n (ET.n (ET.e 113 20567 246) (ET.e 1493 20903 238)) (ET.n (ET.e 10589 21179 232) (ET.n (ET.e 269 21521 224) (ET.e 23 21851 217))))) (ET.n (ET.n (ET.n (ET.e 17 22271 208) (ET.e 1607 22499 203)) (ET.n (ET.e 29 22853 197) (ET.n (ET.e 17 23189 189) (ET.e 2927 23417 185)))) (ET.n (ET.n (ET.e 383 23747 179) (ET.e 17 24107 173)) (ET.n (ET.e 557 24509 166) (ET.n (ET.e 17 24821 161) (ET.e 197 25217 155)))))))
private def etCase1_3 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 29 59 165339) (ET.e 5 191 50980)) (ET.n (ET.e 5 401 24208) (ET.e 5 641 15085))) (ET.n (ET.n (ET.e 5 881 10923) (ET.e 5 1031 9311)) (ET.n (ET.e 149 1193 8020) (ET.n (ET.e 683 1367 6978) (ET.e 809 1619 5862))))) (ET.n (ET.n (ET.n (ET.e 17 1973 4775) (ET.e 53 2333 4008)) (ET.n (ET.e 1229 2459 3790) (ET.e 17 2789 3320))) (ET.n (ET.n (ET.e 23 3083 2982) (ET.e 29 3539 2571)) (ET.n (ET.e 53 3923 2298) (ET.n (ET.e 17 4217 2125) (ET.e 17 4523 1965)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 617 4937 1781) (ET.e 263 5261 1660)) (ET.n (ET.e 2753 5507 1577) (ET.e 419 5867 1464))) (ET.n (ET.n (ET.e 29 6323 1342) (ET.e 857 6857 1221)) (ET.n (ET.e 53 7103 1171) (ET.n (ET.e 23 7499 1097) (ET.e 3863 7727 1058))))) (ET.n (ET.n (ET.n (ET.e 113 8363 960) (ET.e 23 8741 908)) (ET.n (ET.e 659 9227 848) (ET.n (ET.e 23 9431 824) (ET.e 113 9719 794)))) (ET.n (ET.n (ET.e 17 9929 771) (ET.e 509 10181 746)) (ET.n (ET.e 5303 10607 708) (ET.n (ET.e 23 11087 667) (ET.e 5741 11483 635))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 5903 11807 611) (ET.e 6101 12203 583)) (ET.n (ET.e 1559 12473 566) (ET.e 6521 13043 531))) (ET.n (ET.n (ET.e 29 13457 507) (ET.e 53 13781 489)) (ET.n (ET.e 29 14327 462) (ET.n (ET.e 17 14723 442) (ET.e 83 15107 425))))) (ET.n (ET.n (ET.n (ET.e 7691 15383 413) (ET.e 197 15761 397)) (ET.n (ET.e 8069 16139 382) (ET.e 23 16607 364))) (ET.n (ET.n (ET.e 8513 17027 350) (ET.e 8663 17327 339)) (ET.n (ET.e 467 17747 325) (ET.n (ET.e 17 18089 314) (ET.e 9209 18419 304)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 9371 18743 294) (ET.e 9539 19079 285)) (ET.n (ET.e 1409 19727 267) (ET.e 10091 20183 256))) (ET.n (ET.n (ET.e 10313 20627 245) (ET.e 29 20939 238)) (ET.n (ET.e 10613 21227 231) (ET.n (ET.e 17 21557 223) (ET.e 17 21863 217))))) (ET.n (ET.n (ET.n (ET.e 857 22283 208) (ET.e 23 22541 202)) (ET.n (ET.e 11471 22943 195) (ET.n (ET.e 29 23201 189) (ET.e 617 23447 185)))) (ET.n (ET.n (ET.e 17 23801 179) (ET.e 23 24197 171)) (ET.n (ET.e 29 24593 164) (ET.n (ET.e 17 24923 159) (ET.e 17 25229 154)))))))
private def etCase1_4 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 5 71 137380) (ET.e 113 227 42876)) (ET.n (ET.e 5 431 22514) (ET.e 17 647 14944))) (ET.n (ET.n (ET.e 5 911 10558) (ET.e 5 1061 9043)) (ET.n (ET.e 17 1259 7591) (ET.n (ET.e 23 1427 6673) (ET.e 17 1667 5688))))) (ET.n (ET.n (ET.n (ET.e 23 1979 4760) (ET.e 5 2351 3976)) (ET.n (ET.e 5 2531 3677) (ET.e 5 2801 580))) (ET.n (ET.n (ET.e 1559 3119 2946) (ET.e 449 3593 2530)) (ET.n (ET.e 2003 4007 2246) (ET.n (ET.e 53 4241 2112) (ET.e 2273 4547 1954)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 353 4943 1779) (ET.e 659 5273 1655)) (ET.n (ET.e 89 5519 1573) (ET.e 2963 5927 1447))) (ET.n (ET.n (ET.e 113 6329 1341) (ET.e 17 6869 1218)) (ET.n (ET.e 89 7121 1167) (ET.n (ET.e 3761 7523 1092) (ET.e 977 7817 1043))))) (ET.n (ET.n (ET.n (ET.e 4211 8423 951) (ET.e 4373 8747 907)) (ET.n (ET.e 149 9239 847) (ET.n (ET.e 4733 9467 820) (ET.e 4871 9743 790)))) (ET.n (ET.n (ET.e 5003 10007 764) (ET.e 269 10223 742)) (ET.n (ET.e 5333 10667 701) (ET.n (ET.e 797 11159 660) (ET.e 359 11489 635))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 11867 607) (ET.e 6113 12227 582)) (ET.n (ET.e 17 12479 566) (ET.e 6551 13103 527))) (ET.n (ET.n (ET.e 53 13463 506) (ET.e 173 13841 486)) (ET.n (ET.e 449 14369 460) (ET.n (ET.e 389 14783 440) (ET.e 17 15131 424))))) (ET.n (ET.n (ET.n (ET.e 773 15461 410) (ET.e 359 15797 395)) (ET.n (ET.e 23 16193 380) (ET.e 17 16661 362))) (ET.n (ET.n (ET.e 2129 17033 350) (ET.e 17 17477 334)) (ET.n (ET.e 17 17783 324) (ET.n (ET.e 9059 18119 313) (ET.e 419 18437 304)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 18803 293) (ET.e 17 19211 282)) (ET.n (ET.e 23 19781 266) (ET.e 17 20231 255))) (ET.n (ET.n (ET.e 17 20639 244) (ET.e 1049 20981 237)) (ET.n (ET.e 1523 21323 228) (ET.n (ET.e 10781 21563 223) (ET.e 17 22067 213))))) (ET.n (ET.n (ET.n (ET.e 29 22331 207) (ET.e 17 22577 202)) (ET.n (ET.e 53 23003 194) (ET.n (ET.e 113 23279 188) (ET.e 317 23459 185)))) (ET.n (ET.n (ET.e 11909 23819 178) (ET.e 12101 24203 171)) (ET.n (ET.e 23 24611 164) (ET.n (ET.e 1787 25019 158) (ET.e 12641 25283 153)))))))
private def etCase1_5 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 5 101 96529) (ET.e 29 233 41769)) (ET.n (ET.e 17 443 21900) (ET.e 5 701 13773))) (ET.n (ET.n (ET.e 29 929 10350) (ET.e 5 1091 8790)) (ET.n (ET.e 29 1277 7481) (ET.n (ET.e 5 1451 6560) (ET.e 53 1697 5585))))) (ET.n (ET.n (ET.n (ET.e 5 2081 4515) (ET.e 5 2381 3924)) (ET.n (ET.e 5 2591 3587) (ET.e 1409 2819 3283))) (ET.n (ET.n (ET.e 29 3191 2875) (ET.e 113 3617 2512)) (ET.n (ET.e 17 4013 2243) (ET.n (ET.e 2129 4259 2102) (ET.e 29 4583 1937)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 113 4973 1767) (ET.e 29 5279 1653)) (ET.n (ET.e 113 5651 1529) (ET.e 23 5981 1432))) (ET.n (ET.n (ET.e 17 6359 1333) (ET.e 3449 6899 1211)) (ET.n (ET.e 509 7127 1166) (ET.n (ET.e 29 7541 1089) (ET.e 563 7883 1032))))) (ET.n (ET.n (ET.n (ET.e 17 8501 941) (ET.e 4391 8783 903)) (ET.n (ET.e 89 9257 845) (ET.n (ET.e 677 9479 819) (ET.e 257 9767 788)))) (ET.n (ET.n (ET.e 503 10061 759) (ET.e 23 10259 739)) (ET.n (ET.e 17 10847 686) (ET.n (ET.e 563 11261 652) (ET.e 827 11579 628))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 1487 11897 605) (ET.e 29 12239 581)) (ET.n (ET.e 6263 12527 563) (ET.e 29 13109 527))) (ET.n (ET.n (ET.e 17 13499 505) (ET.e 17 13907 482)) (ET.n (ET.e 7211 14423 456) (ET.n (ET.e 23 14813 438) (ET.e 23 15227 419))))) (ET.n (ET.n (ET.n (ET.e 149 15497 408) (ET.e 7901 15803 395)) (ET.n (ET.e 2027 16217 379) (ET.e 17 16763 359))) (ET.n (ET.n (ET.e 449 17063 348) (ET.e 23 17573 331)) (ET.n (ET.e 29 17807 324) (ET.n (ET.e 17 18191 311) (ET.e 9221 18443 304)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2357 18857 291) (ET.e 23 19367 277)) (ET.n (ET.e 113 19889 263) (ET.e 17 20333 253))) (ET.n (ET.n (ET.e 10331 20663 244) (ET.e 23 21023 236)) (ET.n (ET.e 17 21353 228) (ET.n (ET.e 10799 21599 222) (ET.e 89 22073 213))))) (ET.n (ET.n (ET.n (ET.e 11171 22343 206) (ET.e 263 22619 201)) (ET.n (ET.e 29 23027 193) (ET.n (ET.e 17 23291 188) (ET.e 29 23549 183)))) (ET.n (ET.n (ET.e 11939 23879 177) (ET.e 3041 24329 169)) (ET.n (ET.e 17 24617 164) (ET.n (ET.e 569 25037 157) (ET.e 23 25301 152)))))))
private def etCase1_6 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 53 107 91110) (ET.e 17 239 40717)) (ET.n (ET.e 5 461 21040) (ET.e 359 719 13425))) (ET.n (ET.n (ET.e 5 941 10216) (ET.e 29 1103 8693)) (ET.n (ET.e 23 1289 7410) (ET.n (ET.e 5 1481 6424) (ET.e 5 1721 5505))))) (ET.n (ET.n (ET.n (ET.e 149 2087 4501) (ET.e 23 2393 3903)) (ET.n (ET.e 5 2621 3544) (ET.e 29 2843 3253))) (ET.n (ET.n (ET.e 23 3221 2847) (ET.e 269 3767 2401)) (ET.n (ET.e 23 4049 2221) (ET.n (ET.e 29 4409 2021) (ET.e 83 4649 1907)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2543 5087 1723) (ET.e 269 5381 1618)) (ET.n (ET.e 29 5801 1483) (ET.e 3023 6047 1415))) (ET.n (ET.n (ET.e 809 6473 1306) (ET.e 23 6947 1201)) (ET.n (ET.e 29 7193 1153) (ET.n (ET.e 947 7577 1083) (ET.e 4019 8039 1008))))) (ET.n (ET.n (ET.n (ET.e 4271 8543 935) (ET.e 17 8807 900)) (ET.n (ET.e 29 9281 842) (ET.n (ET.e 17 9521 815) (ET.e 89 9791 785)))) (ET.n (ET.n (ET.e 5039 10079 757) (ET.e 17 10337 732)) (ET.n (ET.e 89 10859 685) (ET.n (ET.e 1409 11273 651) (ET.e 83 11621 624))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 89 11927 603) (ET.e 6131 12263 579)) (ET.n (ET.e 6269 12539 562) (ET.e 263 13151 525))) (ET.n (ET.n (ET.e 6761 13523 503) (ET.e 17 14009 477)) (ET.n (ET.e 17 14519 452) (ET.n (ET.e 7433 14867 436) (ET.e 17 15233 419))))) (ET.n (ET.n (ET.n (ET.e 1109 15527 407) (ET.e 419 15923 390)) (ET.n (ET.e 8111 16223 379) (ET.e 23 16883 355))) (ET.n (ET.n (ET.e 83 17099 347) (ET.e 17 17579 331)) (ET.n (ET.e 8951 17903 320) (ET.n (ET.e 479 18203 311) (ET.e 29 18503 302)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 53 18869 291) (ET.e 29 19373 277)) (ET.n (ET.e 23 19919 262) (ET.e 2549 20393 250))) (ET.n (ET.n (ET.e 23 20747 242) (ET.e 10529 21059 235)) (ET.n (ET.e 10691 21383 227) (ET.n (ET.e 293 21683 221) (ET.e 83 22079 213))))) (ET.n (ET.n (ET.n (ET.e 53 22367 206) (ET.e 11321 22643 201)) (ET.n (ET.e 11519 23039 193) (ET.n (ET.e 53 23321 187) (ET.e 11783 23567 183)))) (ET.n (ET.n (ET.e 53 23957 176) (ET.e 17 24413 167)) (ET.n (ET.e 947 24623 164) (ET.n (ET.e 3137 25097 156) (ET.e 12653 25307 152)))))))
private def etCase1_7 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 5 131 74399) (ET.e 5 251 38765)) (ET.n (ET.e 5 491 19736) (ET.e 53 743 12986))) (ET.n (ET.n (ET.e 17 953 10086) (ET.e 5 1151 8318)) (ET.n (ET.e 5 1301 7340) (ET.n (ET.e 5 1511 6293) (ET.e 5 1811 5218))))) (ET.n (ET.n (ET.n (ET.e 1049 2099 4474) (ET.e 5 2411 3873)) (ET.n (ET.e 83 2657 3494) (ET.e 1439 2879 3211))) (ET.n (ET.n (ET.e 17 3299 2772) (ET.e 1889 3779 2393)) (ET.n (ET.e 509 4073 2207) (ET.n (ET.e 17 4421 2015) (ET.e 2339 4679 1893)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2549 5099 1719) (ET.e 2693 5387 1616)) (ET.n (ET.e 2903 5807 1481) (ET.e 17 6053 1412))) (ET.n (ET.n (ET.e 17 6563 1286) (ET.e 17 6971 1197)) (ET.n (ET.e 3623 7247 1142) (ET.n (ET.e 17 7583 1082) (ET.e 17 8093 999))))) (ET.n (ET.n (ET.n (ET.e 269 8609 925) (ET.e 29 8933 884)) (ET.n (ET.e 23 9293 841) (ET.n (ET.e 4793 9587 808) (ET.e 29 9803 784)))) (ET.n (ET.n (ET.e 5051 10103 755) (ET.e 5171 10343 731)) (ET.n (ET.e 17 10949 678) (ET.n (ET.e 5639 11279 651) (ET.e 23 11639 623))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 11969 600) (ET.e 23 12329 575)) (ET.n (ET.e 23 12743 548) (ET.e 6581 13163 524))) (ET.n (ET.n (ET.e 83 13613 498) (ET.e 17 14111 472)) (ET.n (ET.e 23 14537 451) (ET.n (ET.e 173 14879 435) (ET.e 7649 15299 416))))) (ET.n (ET.n (ET.n (ET.e 17 15641 403) (ET.e 53 16007 387)) (ET.n (ET.e 29 16241 378) (ET.e 29 16937 353))) (ET.n (ET.n (ET.e 389 17117 346) (ET.e 53 17597 330)) (ET.n (ET.e 8969 17939 319) (ET.n (ET.e 569 18209 310) (ET.e 23 18539 301)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 9461 18923 289) (ET.e 89 19403 277)) (ET.n (ET.e 89 19937 262) (ET.e 10253 20507 247))) (ET.n (ET.n (ET.e 1487 20819 240) (ET.e 659 21089 234)) (ET.n (ET.e 10709 21419 226) (ET.n (ET.e 23 21713 220) (ET.e 503 22133 211))))) (ET.n (ET.n (ET.n (ET.e 509 22397 205) (ET.e 17 22679 200)) (ET.n (ET.e 887 23063 193) (ET.n (ET.e 23 23369 186) (ET.e 11801 23603 182)))) (ET.n (ET.n (ET.e 12011 24023 175) (ET.e 29 24419 167)) (ET.n (ET.e 89 24743 162) (ET.n (ET.e 17 25127 156) (ET.e 12671 25343 152)))))))
private def etCase1 : ET :=
  ET.n (ET.n (ET.n etCase1_0 etCase1_1) (ET.n etCase1_2 etCase1_3)) (ET.n (ET.n etCase1_4 etCase1_5) (ET.n etCase1_6 etCase1_7))

private def etCase2_0 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 29 336487) (ET.e 17 137 71136)) (ET.n (ET.e 19 229 42501) (ET.e 173 347 27995))) (ET.n (ET.n (ET.e 19 457 21225) (ET.e 7 617 15677)) (ET.n (ET.e 359 719 13425) (ET.n (ET.e 13 859 11213) (ET.e 7 1009 9517))))) (ET.n (ET.n (ET.n (ET.e 17 1123 8530) (ET.e 13 1327 7193)) (ET.n (ET.e 7 1499 6345) (ET.e 67 1609 5899))) (ET.n (ET.n (ET.e 433 1733 5460) (ET.e 59 1889 4995)) (ET.n (ET.e 7 2017 4667) (ET.n (ET.e 367 2203 4255) (ET.e 7 2339 3997)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 2437 3825) (ET.e 83 2657 3494)) (ET.n (ET.e 7 2843 3253) (ET.e 7 2969 3104))) (ET.n (ET.n (ET.e 7 3137 2928) (ET.e 7 3319 2754)) (ET.n (ET.e 13 3433 2656) (ET.n (ET.e 59 3659 2481) (ET.e 7 3823 2363))))) (ET.n (ET.n (ET.n (ET.e 23 4003 2249) (ET.e 2063 4127 2175)) (ET.n (ET.e 7 4243 2111) (ET.n (ET.e 67 4423 2014) (ET.e 383 4597 1931)))) (ET.n (ET.n (ET.e 7 4733 1870) (ET.e 7 4957 1773)) (ET.n (ET.e 83 5147 1701) (ET.n (ET.e 109 5233 1670) (ET.e 227 5449 1596))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 23 5659 1526) (ET.e 1453 5813 1479)) (ET.n (ET.e 7 5923 1448) (ET.e 23 6073 1407))) (ET.n (ET.n (ET.e 173 6229 1366) (ET.e 7 6343 1337)) (ET.n (ET.e 809 6473 1306) (ET.n (ET.e 19 6689 1257) (ET.e 7 6833 1226))))) (ET.n (ET.n (ET.n (ET.e 7 6959 1199) (ET.e 7 7127 1166)) (ET.n (ET.e 7 7253 1141) (ET.n (ET.e 7 7477 1101) (ET.e 947 7577 1083)))) (ET.n (ET.n (ET.e 1283 7699 1062) (ET.e 19 7829 1041)) (ET.n (ET.e 37 7993 1015) (ET.n (ET.e 13 8243 977) (ET.e 7 8387 956)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 97 8537 936) (ET.e 4373 8747 907)) (ET.n (ET.e 1487 8923 885) (ET.e 23 9109 862))) (ET.n (ET.n (ET.e 7 9283 842) (ET.e 7 9437 824)) (ET.n (ET.e 4793 9587 808) (ET.n (ET.e 19 9767 788) (ET.e 13 9907 774))))) (ET.n (ET.n (ET.n (ET.e 17 10099 755) (ET.e 233 10253 739)) (ET.n (ET.e 13 10427 724) (ET.n (ET.e 7 10529 714) (ET.e 13 10687 700)))) (ET.n (ET.n (ET.e 2713 10853 686) (ET.e 7 11047 670)) (ET.n (ET.e 7 11159 660) (ET.n (ET.e 7 11299 649) (ET.e 7 11467 637)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 727 11633 623) (ET.e 13 11779 613)) (ET.n (ET.e 13 11909 604) (ET.e 17 12037 595))) (ET.n (ET.n (ET.e 23 12329 575) (ET.e 17 12479 566)) (ET.n (ET.e 13 12637 555) (ET.n (ET.e 7 12853 542) (ET.e 3259 13037 531))))) (ET.n (ET.n (ET.n (ET.e 59 13217 520) (ET.e 17 13397 510)) (ET.n (ET.e 83 13613 498) (ET.e 2287 13723 493))) (ET.n (ET.n (ET.e 769 13843 486) (ET.e 3499 13997 478)) (ET.n (ET.e 1193 14317 462) (ET.n (ET.e 17 14519 452) (ET.e 59 14633 446)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 14723 442) (ET.e 13 14873 436)) (ET.n (ET.e 3793 15173 422) (ET.e 7643 15287 417))) (ET.n (ET.n (ET.e 19 15467 410) (ET.e 373 15667 401)) (ET.n (ET.e 83 15937 390) (ET.n (ET.e 577 16157 382) (ET.e 13 16433 370))))) (ET.n (ET.n (ET.n (ET.e 19 16607 364) (ET.e 109 16787 358)) (ET.n (ET.e 257 16963 352) (ET.n (ET.e 23 17113 346) (ET.e 619 17333 339)))) (ET.n (ET.n (ET.e 17 17443 335) (ET.e 83 17597 330)) (ET.n (ET.e 17 17783 324) (ET.n (ET.e 73 17959 318) (ET.e 19 18127 313))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 4567 18269 309) (ET.e 13 18539 301)) (ET.n (ET.e 13 18773 293) (ET.e 19 19153 283))) (ET.n (ET.n (ET.e 13 19319 279) (ET.e 17 19483 274)) (ET.n (ET.e 13 19709 268) (ET.n (ET.e 23 19919 262) (ET.e 1433 20063 259))))) (ET.n (ET.n (ET.n (ET.e 563 20269 254) (ET.e 19 20369 251)) (ET.n (ET.e 13 20593 245) (ET.n (ET.e 13 20749 242) (ET.e 109 20929 238)))) (ET.n (ET.n (ET.e 17 21149 233) (ET.e 17 21319 228)) (ET.n (ET.e 13 21503 224) (ET.n (ET.e 257 21589 223) (ET.e 10883 21767 219)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 13 21997 214) (ET.e 5527 22109 212)) (ET.n (ET.e 5569 22277 208) (ET.e 1879 22549 202))) (ET.n (ET.n (ET.e 13 22699 199) (ET.e 5743 22973 194)) (ET.n (ET.e 11549 23099 192) (ET.n (ET.e 17 23393 186) (ET.e 17 23563 183))))) (ET.n (ET.n (ET.n (ET.e 1319 23743 180) (ET.e 13 23869 177)) (ET.n (ET.e 13 24077 174) (ET.n (ET.e 13 24337 169) (ET.e 227 24517 166)))) (ET.n (ET.n (ET.e 23 24749 162) (ET.e 23 24979 158)) (ET.n (ET.e 23 25163 155) (ET.n (ET.e 6337 25349 152) (ET.e 6367 25469 150))))))))
private def etCase2_1 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 43 226892) (ET.e 23 139 70111)) (ET.n (ET.e 7 239 40717) (ET.e 7 379 25620))) (ET.n (ET.n (ET.e 7 463 20948) (ET.e 107 643 15037)) (ET.n (ET.e 7 743 12986) (ET.n (ET.e 73 877 10973) (ET.e 23 1013 9479))))) (ET.n (ET.n (ET.n (ET.e 7 1163 8231) (ET.e 683 1367 6978)) (ET.n (ET.e 257 1543 6159) (ET.e 13 1613 5884))) (ET.n (ET.n (ET.e 97 1747 5415) (ET.e 7 1933 4878)) (ET.n (ET.e 13 2029 4639) (ET.n (ET.e 7 2213 4235) (ET.e 17 2347 3983)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 1229 2459 3790) (ET.e 17 2687 3453)) (ET.n (ET.e 7 2857 3237) (ET.e 503 3019 3049))) (ET.n (ET.n (ET.e 17 3163 2902) (ET.e 13 3329 2745)) (ET.n (ET.e 577 3463 2632) (ET.n (ET.e 17 3673 2471) (ET.e 479 3833 2357))))) (ET.n (ET.n (ET.n (ET.e 17 4013 2243) (ET.e 1033 4133 2172)) (ET.n (ET.e 89 4273 2095) (ET.n (ET.e 13 4447 2002) (ET.e 13 4603 1928)))) (ET.n (ET.n (ET.e 13 4759 1858) (ET.e 13 4967 1769)) (ET.n (ET.e 7 5153 1699) (ET.n (ET.e 7 5237 1668) (ET.e 37 5477 1586))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 5669 1523) (ET.e 7 5839 1472)) (ET.n (ET.e 2963 5927 1447) (ET.e 7 6133 1391))) (ET.n (ET.n (ET.e 17 6257 1359) (ET.e 397 6353 1335)) (ET.n (ET.e 17 6529 1293) (ET.n (ET.e 1117 6703 1254) (ET.e 73 6863 1220))))) (ET.n (ET.n (ET.n (ET.e 109 6977 1195) (ET.e 1193 7159 1160)) (ET.n (ET.e 19 7297 1133) (ET.e 19 7487 1099))) (ET.n (ET.n (ET.e 17 7583 1082) (ET.e 13 7723 1058)) (ET.n (ET.e 13 7853 1036) (ET.n (ET.e 7 8009 1012) (ET.e 17 8263 974)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 233 8389 956) (ET.e 1423 8539 935)) (ET.n (ET.e 7 8779 903) (ET.e 7 8933 884))) (ET.n (ET.n (ET.e 13 9127 860) (ET.e 23 9293 841)) (ET.n (ET.e 13 9439 824) (ET.n (ET.e 89 9613 805) (ET.e 37 9769 788))))) (ET.n (ET.n (ET.n (ET.e 17 9929 771) (ET.e 17 10133 752)) (ET.n (ET.e 23 10259 739) (ET.n (ET.e 163 10433 723) (ET.e 587 10567 711)))) (ET.n (ET.n (ET.e 2677 10709 698) (ET.e 89 10859 685)) (ET.n (ET.e 19 11059 669) (ET.n (ET.e 7 11173 659) (ET.e 23 11317 648)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 359 11489 635) (ET.e 23 11639 623)) (ET.n (ET.e 7 11789 612) (ET.e 1987 11923 603))) (ET.n (ET.n (ET.e 503 12073 593) (ET.e 17 12343 574)) (ET.n (ET.e 7 12503 564) (ET.n (ET.e 13 12689 552) (ET.e 3229 12917 538))))) (ET.n (ET.n (ET.n (ET.e 7 13049 530) (ET.e 23 13249 518)) (ET.n (ET.e 13 13417 509) (ET.e 619 13619 498))) (ET.n (ET.n (ET.e 13 13729 492) (ET.e 13 13859 485)) (ET.n (ET.e 2333 13999 478) (ET.n (ET.e 13 14327 462) (ET.e 173 14533 451)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 13 14639 446) (ET.e 73 14747 441)) (ET.n (ET.e 173 14879 435) (ET.e 17 15199 421))) (ET.n (ET.n (ET.e 13 15289 417) (ET.e 13 15497 408)) (ET.n (ET.e 13 15679 401) (ET.n (ET.e 2677 16063 385) (ET.e 19 16189 380))))) (ET.n (ET.n (ET.n (ET.e 13 16459 369) (ET.e 1187 16619 364)) (ET.n (ET.e 37 16799 357) (ET.n (ET.e 13 16979 351) (ET.e 17 17137 345)))) (ET.n (ET.n (ET.e 263 17359 338) (ET.e 727 17449 335)) (ET.n (ET.e 89 17623 329) (ET.n (ET.e 59 17819 323) (ET.e 107 17977 317))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 193 18143 312) (ET.e 109 18313 307)) (ET.n (ET.e 19 18583 300) (ET.e 37 18797 293))) (ET.n (ET.n (ET.e 13 19163 283) (ET.e 23 19367 277)) (ET.n (ET.e 3253 19519 273) (ET.n (ET.e 1409 19727 267) (ET.e 89 19937 262))))) (ET.n (ET.n (ET.n (ET.e 1117 20107 258) (ET.e 23 20287 254)) (ET.n (ET.e 19 20407 250) (ET.n (ET.e 10313 20627 245) (ET.e 1297 20753 242)))) (ET.n (ET.n (ET.e 19 20939 238) (ET.e 3527 21163 233)) (ET.n (ET.e 1523 21323 228) (ET.n (ET.e 19 21509 224) (ET.e 193 21617 222)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 173 21799 218) (ET.e 19 22003 214)) (ET.n (ET.e 1229 22123 212) (ET.e 13 22283 208))) (ET.n (ET.n (ET.e 19 22573 202) (ET.e 1033 22727 199)) (ET.n (ET.e 1277 22987 194) (ET.n (ET.e 19 23143 191) (ET.e 11699 23399 186))))) (ET.n (ET.n (ET.n (ET.e 11783 23567 183) (ET.e 383 23747 179)) (ET.n (ET.e 373 23873 177) (ET.n (ET.e 13 24103 173) (ET.e 19 24359 168)))) (ET.n (ET.n (ET.e 67 24523 165) (ET.e 1033 24793 161)) (ET.n (ET.e 6247 24989 158) (ET.n (ET.e 13 25169 155) (ET.e 2113 25357 151))))))))
private def etCase2_2 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 23 47 207575) (ET.e 37 149 65399)) (ET.n (ET.e 67 269 36163) (ET.e 97 389 24958))) (ET.n (ET.n (ET.e 233 467 20768) (ET.e 17 647 14944)) (ET.n (ET.e 7 757 12743) (ET.n (ET.e 7 883 10898) (ET.e 509 1019 9423))))) (ET.n (ET.n (ET.n (ET.e 19 1217 7858) (ET.e 7 1373 6947)) (ET.n (ET.e 97 1553 6118) (ET.e 809 1619 5862))) (ET.n (ET.n (ET.e 73 1753 5396) (ET.e 487 1949 4836)) (ET.n (ET.e 19 2053 4579) (ET.n (ET.e 13 2237 4187) (ET.e 19 2357 3965)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 619 2477 3761) (ET.e 7 2689 3450)) (ET.n (ET.e 1439 2879 3211) (ET.e 23 3037 3030))) (ET.n (ET.n (ET.e 59 3187 2879) (ET.e 557 3343 2733)) (ET.n (ET.e 17 3469 2627) (ET.n (ET.e 7 3697 2453) (ET.e 107 3853 2344))))) (ET.n (ET.n (ET.n (ET.e 7 4019 2239) (ET.e 2069 4139 2169)) (ET.n (ET.e 67 4289 2083) (ET.n (ET.e 557 4457 1997) (ET.e 19 4637 1912)))) (ET.n (ET.n (ET.e 7 4789 1846) (ET.e 23 4969 1769)) (ET.n (ET.e 7 5167 1693) (ET.n (ET.e 7 5279 1653) (ET.e 83 5479 1586))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 947 5683 1519) (ET.e 23 5843 1471)) (ET.n (ET.e 73 5987 1431) (ET.e 37 6143 1388))) (ET.n (ET.n (ET.e 1567 6269 1356) (ET.e 17 6359 1333)) (ET.n (ET.e 7 6553 1288) (ET.n (ET.e 13 6709 1252) (ET.e 17 6869 1218))))) (ET.n (ET.n (ET.n (ET.e 17 7039 1183) (ET.e 13 7177 1156)) (ET.n (ET.e 13 7307 1131) (ET.e 13 7489 1099))) (ET.n (ET.n (ET.e 7 7589 1081) (ET.e 3863 7727 1058)) (ET.n (ET.e 19 7867 1034) (ET.n (ET.e 17 8059 1005) (ET.e 13 8269 973)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 23 8419 952) (ET.e 7 8597 927)) (ET.n (ET.e 163 8803 900) (ET.e 19 8969 879))) (ET.n (ET.n (ET.e 7 9157 856) (ET.e 59 9323 837)) (ET.n (ET.e 19 9463 821) (ET.n (ET.e 7 9619 804) (ET.e 7 9787 786))))) (ET.n (ET.n (ET.n (ET.e 5003 10007 764) (ET.e 37 10139 751)) (ET.n (ET.e 59 10267 738) (ET.n (ET.e 13 10453 721) (ET.e 5303 10607 708)))) (ET.n (ET.n (ET.e 2683 10733 696) (ET.e 23 10903 682)) (ET.n (ET.e 2767 11069 668) (ET.n (ET.e 2803 11213 656) (ET.e 59 11329 647)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 479 11497 634) (ET.e 7 11663 621)) (ET.n (ET.e 2953 11813 611) (ET.e 67 11927 603))) (ET.n (ET.n (ET.e 7 12097 591) (ET.e 6173 12347 574)) (ET.n (ET.e 7 12517 563) (ET.n (ET.e 23 12697 551) (ET.e 2153 12919 538))))) (ET.n (ET.n (ET.n (ET.e 7 13063 530) (ET.e 947 13259 518)) (ET.n (ET.e 13 13469 506) (ET.e 853 13649 497))) (ET.n (ET.n (ET.e 19 13757 491) (ET.e 17 13873 484)) (ET.n (ET.e 17 14009 477) (ET.n (ET.e 7193 14387 459) (ET.e 23 14537 451)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 37 14653 446) (ET.e 23 14767 440)) (ET.n (ET.e 19 14897 435) (ET.e 317 15217 420))) (ET.n (ET.n (ET.e 7649 15299 416) (ET.e 1109 15527 407)) (ET.n (ET.e 19 15733 398) (ET.n (ET.e 13 16069 385) (ET.e 23 16193 380))))) (ET.n (ET.n (ET.n (ET.e 19 16493 368) (ET.e 13 16693 361)) (ET.n (ET.e 13 16823 357) (ET.n (ET.e 19 16987 351) (ET.e 23 17159 344)))) (ET.n (ET.n (ET.e 2897 17383 337) (ET.e 17 17477 334)) (ET.n (ET.e 2207 17657 328) (ET.n (ET.e 13 17837 323) (ET.e 17 17987 317))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 18149 312) (ET.e 37 18353 306)) (ET.n (ET.e 83 18593 299) (ET.e 17 18803 293))) (ET.n (ET.n (ET.e 17 19177 282) (ET.e 359 19387 277)) (ET.n (ET.e 13 19553 272) (ET.n (ET.e 823 19753 267) (ET.e 3323 19939 262))))) (ET.n (ET.n (ET.n (ET.e 107 20117 258) (ET.e 59 20297 253)) (ET.n (ET.e 13 20437 249) (ET.n (ET.e 17 20639 244) (ET.e 97 20759 242)))) (ET.n (ET.n (ET.e 13 20983 237) (ET.e 10589 21179 232)) (ET.n (ET.e 13 21347 228) (ET.n (ET.e 163 21517 224) (ET.e 37 21683 221)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 3637 21823 218) (ET.e 787 22037 213)) (ET.n (ET.e 503 22133 211) (ET.e 59 22303 207))) (ET.n (ET.n (ET.e 17 22577 202) (ET.e 1423 22769 198)) (ET.n (ET.e 479 22993 194) (ET.n (ET.e 13 23167 191) (ET.e 19 23447 185))))) (ET.n (ET.n (ET.n (ET.e 983 23593 182) (ET.e 17 23767 179)) (ET.n (ET.e 11939 23879 177) (ET.n (ET.e 17 24107 173) (ET.e 17 24379 168)))) (ET.n (ET.n (ET.e 12263 24527 165) (ET.e 13 24883 160)) (ET.n (ET.e 13 25013 158) (ET.n (ET.e 17 25229 154) (ET.e 1153 25367 151))))))))
private def etCase2_3 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 53 184066) (ET.e 13 157 62061)) (ET.n (ET.e 23 277 35115) (ET.e 17 409 23732))) (ET.n (ET.n (ET.e 83 499 19418) (ET.e 163 653 14805)) (ET.n (ET.e 193 773 12477) (ET.n (ET.e 17 919 10465) (ET.e 173 1039 9238))))) (ET.n (ET.n (ET.n (ET.e 13 1223 7819) (ET.e 233 1399 6810)) (ET.n (ET.e 19 1559 6094) (ET.e 23 1657 5724))) (ET.n (ET.n (ET.e 37 1777 5321) (ET.e 17 1973 4775)) (ET.n (ET.e 7 2087 4501) (ET.n (ET.e 373 2239 4184) (ET.e 397 2383 3920)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 2549 3649) (ET.e 19 2699 3437)) (ET.n (ET.e 13 2887 3201) (ET.e 7 3067 2999))) (ET.n (ET.n (ET.e 67 3217 2850) (ET.e 7 3347 2730)) (ET.n (ET.e 7 3529 2579) (ET.n (ET.e 13 3719 2438) (ET.e 17 3877 2328))))) (ET.n (ET.n (ET.n (ET.e 23 4049 2221) (ET.e 173 4153 2161)) (ET.n (ET.e 7 4327 2063) (ET.n (ET.e 23 4463 1994) (ET.e 7 4649 1907)))) (ET.n (ET.n (ET.e 7 4817 1834) (ET.e 13 4993 1759)) (ET.n (ET.e 863 5179 1689) (ET.n (ET.e 887 5323 1638) (ET.e 7 5503 1578))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 1423 5693 1516) (ET.e 17 5849 1469)) (ET.n (ET.e 7 6007 1425) (ET.e 13 6163 1383))) (ET.n (ET.n (ET.e 523 6277 1354) (ET.e 59 6373 1330)) (ET.n (ET.e 17 6563 1286) (ET.n (ET.e 17 6733 1247) (ET.e 37 6883 1215))))) (ET.n (ET.n (ET.n (ET.e 7 7043 1182) (ET.e 3593 7187 1155)) (ET.n (ET.e 7 7309 1131) (ET.e 23 7499 1097))) (ET.n (ET.n (ET.e 7 7603 1078) (ET.e 17 7753 1053)) (ET.n (ET.e 13 7879 1032) (ET.n (ET.e 13 8087 1000) (ET.e 17 8297 969)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 8429 950) (ET.e 1433 8599 927)) (ET.n (ET.e 7 8807 900) (ET.e 19 9007 874))) (ET.n (ET.n (ET.e 2293 9173 854) (ET.e 173 9343 834)) (ET.n (ET.e 37 9473 820) (ET.n (ET.e 17 9623 804) (ET.e 13 9803 784))))) (ET.n (ET.n (ET.n (ET.e 13 10037 761) (ET.e 1693 10159 749)) (ET.n (ET.e 107 10273 738) (ET.n (ET.e 1307 10457 721) (ET.e 13 10609 707)))) (ET.n (ET.n (ET.e 7 10739 695) (ET.e 1823 10939 679)) (ET.n (ET.e 23 11087 667) (ET.n (ET.e 7 11243 654) (ET.e 7 11369 644)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 11519 633) (ET.e 7 11677 620)) (ET.n (ET.e 73 11827 610) (ET.e 19 11933 602))) (ET.n (ET.n (ET.e 73 12119 589) (ET.e 7 12377 572)) (ET.n (ET.e 6263 12527 563) (ET.n (ET.e 73 12703 551) (ET.e 7 12923 538))))) (ET.n (ET.n (ET.n (ET.e 37 13099 528) (ET.e 67 13267 517)) (ET.n (ET.e 3373 13493 505) (ET.e 17 13669 496))) (ET.n (ET.n (ET.e 2293 13759 491) (ET.e 257 13879 484)) (ET.n (ET.e 73 14017 477) (ET.n (ET.e 109 14389 458) (ET.e 3637 14549 450)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 349 14659 445) (ET.e 19 14783 440)) (ET.n (ET.e 3733 14933 433) (ET.e 23 15227 419))) (ET.n (ET.n (ET.e 23 15319 416) (ET.e 2593 15559 406)) (ET.n (ET.e 359 15797 395) (ET.n (ET.e 383 16087 384) (ET.e 2027 16217 379))))) (ET.n (ET.n (ET.n (ET.e 2753 16519 367) (ET.e 23 16699 361)) (ET.n (ET.e 23 16837 356) (ET.n (ET.e 59 16993 351) (ET.e 4297 17189 343)))) (ET.n (ET.n (ET.e 8693 17387 337) (ET.e 1459 17509 333)) (ET.n (ET.e 109 17659 328) (ET.n (ET.e 13 17863 322) (ET.e 19 18013 316))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 19 18203 311) (ET.e 73 18397 305)) (ET.n (ET.e 13 18617 299) (ET.e 89 18869 291))) (ET.n (ET.n (ET.e 23 19183 282) (ET.e 89 19403 277)) (ET.n (ET.e 2447 19577 271) (ET.n (ET.e 37 19759 266) (ET.e 4987 19949 262))))) (ET.n (ET.n (ET.n (ET.e 17 20129 257) (ET.e 1129 20323 253)) (ET.n (ET.e 5113 20453 249) (ET.n (ET.e 10343 20687 243) (ET.e 577 20773 241)))) (ET.n (ET.n (ET.e 17 21013 236) (ET.e 107 21187 232)) (ET.n (ET.e 17 21353 228) (ET.n (ET.e 17 21523 224) (ET.e 23 21713 220)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 21863 217) (ET.e 3677 22063 213)) (ET.n (ET.e 13 22153 211) (ET.e 19 22307 207))) (ET.n (ET.n (ET.e 5653 22613 201) (ET.e 13 22777 198)) (ET.n (ET.e 397 23027 193) (ET.n (ET.e 17 23189 189) (ET.e 977 23449 185))))) (ET.n (ET.n (ET.n (ET.e 19 23599 182) (ET.e 283 23773 179)) (ET.n (ET.e 569 23899 177) (ET.n (ET.e 19 24169 172) (ET.e 12203 24407 167)))) (ET.n (ET.n (ET.e 17 24617 164) (ET.e 17 24889 160)) (ET.n (ET.e 569 25037 157) (ET.n (ET.e 13 25247 154) (ET.e 907 25397 151))))))))
private def etCase2_4 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 79 123460) (ET.e 83 167 58339)) (ET.n (ET.e 73 293 33191) (ET.e 19 419 23162))) (ET.n (ET.n (ET.e 7 547 17701) (ET.e 7 659 14669)) (ET.n (ET.e 199 797 12096) (ET.n (ET.e 13 937 10261) (ET.e 59 1063 9026))))) (ET.n (ET.n (ET.n (ET.e 13 1249 7653) (ET.e 23 1427 6673)) (ET.n (ET.e 263 1579 6015) (ET.e 7 1667 5688))) (ET.n (ET.n (ET.e 19 1787 5290) (ET.e 23 1979 4760)) (ET.n (ET.e 1049 2099 4474) (ET.n (ET.e 19 2243 4176) (ET.e 199 2389 3910)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 163 2609 3561) (ET.e 17 2789 3320)) (ET.n (ET.e 727 2909 3172) (ET.e 19 3079 2986))) (ET.n (ET.n (ET.e 37 3257 2813) (ET.e 23 3359 2719)) (ET.n (ET.e 7 3557 2557) (ET.n (ET.e 23 3727 2432) (ET.e 7 3907 2309))))) (ET.n (ET.n (ET.n (ET.e 13 4057 2216) (ET.e 7 4159 2157)) (ET.n (ET.e 1087 4349 2052) (ET.n (ET.e 83 4483 1985) (ET.e 97 4657 1903)))) (ET.n (ET.n (ET.e 23 4877 1806) (ET.e 7 4999 1757)) (ET.n (ET.e 1297 5189 1685) (ET.n (ET.e 2693 5387 1616) (ET.e 2753 5507 1577))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 479 5749 1499) (ET.e 7 5867 1464)) (ET.n (ET.e 503 6037 1417) (ET.e 1549 6197 1374))) (ET.n (ET.n (ET.e 7 6287 1352) (ET.e 13 6397 1324)) (ET.n (ET.e 367 6607 1275) (ET.n (ET.e 7 6763 1241) (ET.e 3449 6899 1211))))) (ET.n (ET.n (ET.n (ET.e 7 7057 1180) (ET.e 13 7229 1146)) (ET.n (ET.e 13 7333 1126) (ET.e 1879 7517 1093))) (ET.n (ET.n (ET.e 3803 7607 1078) (ET.e 7 7757 1053)) (ET.n (ET.e 7 7883 1032) (ET.n (ET.e 7 8093 999) (ET.e 7 8317 966)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 8443 948) (ET.e 479 8623 923)) (ET.n (ET.e 7 8849 894) (ET.e 37 9029 871))) (ET.n (ET.n (ET.e 7 9199 851) (ET.e 19 9349 833)) (ET.n (ET.e 7 9479 819) (ET.n (ET.e 83 9629 803) (ET.e 7 9829 781))))) (ET.n (ET.n (ET.n (ET.e 7 10039 761) (ET.e 7 10193 745)) (ET.n (ET.e 17 10303 735) (ET.n (ET.e 7 10459 721) (ET.e 7 10613 707)))) (ET.n (ET.n (ET.e 7 10753 694) (ET.e 7 10949 678)) (ET.n (ET.e 59 11093 666) (ET.n (ET.e 7 11257 653) (ET.e 7 11383 643)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 11527 632) (ET.e 487 11689 619)) (ET.n (ET.e 17 11833 609) (ET.e 83 11953 601))) (ET.n (ET.n (ET.e 13 12143 587) (ET.e 2063 12379 572)) (ET.n (ET.e 17 12547 561) (ET.n (ET.e 7 12713 550) (ET.e 19 12959 536))))) (ET.n (ET.n (ET.n (ET.e 7 13147 498) (ET.e 1109 13309 515)) (ET.n (ET.e 17 13499 505) (ET.e 977 13679 495))) (ET.n (ET.n (ET.e 983 13763 491) (ET.e 17 13907 482)) (ET.n (ET.e 13 14197 468) (ET.n (ET.e 89 14419 456) (ET.e 1213 14557 450)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 14669 445) (ET.e 2467 14803 439)) (ET.n (ET.e 97 14939 433) (ET.e 17 15233 419))) (ET.n (ET.n (ET.e 479 15329 415) (ET.e 17 15607 404)) (ET.n (ET.e 13 15809 395) (ET.n (ET.e 503 16097 384) (ET.e 17 16253 378))))) (ET.n (ET.n (ET.n (ET.e 1033 16529 367) (ET.e 1193 16703 361)) (ET.n (ET.e 97 16879 355) (ET.n (ET.e 947 17047 349) (ET.e 1229 17207 343)))) (ET.n (ET.n (ET.e 23 17389 337) (ET.e 19 17519 333)) (ET.n (ET.e 13 17707 327) (ET.n (ET.e 1489 17869 321) (ET.e 97 18043 315))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 569 18209 310) (ET.e 9209 18419 304)) (ET.n (ET.e 13 18643 298) (ET.e 4729 18917 289))) (ET.n (ET.n (ET.e 97 19207 282) (ET.e 809 19417 276)) (ET.n (ET.e 23 19597 271) (ET.n (ET.e 1237 19793 266) (ET.e 1109 19963 261))))) (ET.n (ET.n (ET.n (ET.e 373 20143 257) (ET.e 10163 20327 253)) (ET.n (ET.e 19 20483 248) (ET.n (ET.e 739 20693 243) (ET.e 17 20809 241)))) (ET.n (ET.n (ET.e 37 21017 236) (ET.e 13 21269 229)) (ET.n (ET.e 509 21379 227) (ET.n (ET.e 13 21529 224) (ET.e 17 21727 220)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 1823 21877 217) (ET.e 17 22067 213)) (ET.n (ET.e 19 22193 209) (ET.e 37 22349 206))) (ET.n (ET.n (ET.e 263 22619 201) (ET.e 23 22817 197)) (ET.n (ET.e 19 23029 193) (ET.n (ET.e 13 23297 187) (ET.e 37 23459 185))))) (ET.n (ET.n (ET.n (ET.e 13 23609 182) (ET.e 19 23789 179)) (ET.n (ET.e 37 23977 176) (ET.n (ET.e 23 24197 171) (ET.e 17 24413 167)))) (ET.n (ET.n (ET.e 13 24623 164) (ET.e 17 24923 159)) (ET.n (ET.e 1567 25073 157) (ET.n (ET.e 59 25253 154) (ET.e 397 25409 151))))))))
private def etCase2_5 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 103 94653) (ET.e 89 179 54421)) (ET.n (ET.e 17 307 31660) (ET.e 73 439 22101))) (ET.n (ET.n (ET.e 37 593 16317) (ET.e 7 673 14353)) (ET.n (ET.e 7 827 11652) (ET.n (ET.e 7 953 10086) (ET.e 89 1069 8975))))) (ET.n (ET.n (ET.n (ET.e 17 1259 7591) (ET.e 7 1429 6663)) (ET.n (ET.e 7 1583 5999) (ET.e 283 1699 5578))) (ET.n (ET.n (ET.e 13 1847 5113) (ET.e 83 1993 4726)) (ET.n (ET.e 7 2129 4409) (ET.n (ET.e 7 2269 4126) (ET.e 13 2393 3903)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 109 2617 3550) (ET.e 233 2797 3310)) (ET.n (ET.e 7 2927 3151) (ET.e 23 3083 2982))) (ET.n (ET.n (ET.e 17 3299 2772) (ET.e 7 3389 2693)) (ET.n (ET.e 199 3583 2537) (ET.n (ET.e 7 3739 2424) (ET.e 89 3917 2302))))) (ET.n (ET.n (ET.n (ET.e 509 4073 2207) (ET.e 17 4217 2125)) (ET.n (ET.e 727 4363 2044) (ET.n (ET.e 1129 4517 1968) (ET.e 7 4663 1901)))) (ET.n (ET.n (ET.e 13 4889 1801) (ET.e 2543 5087 1723)) (ET.n (ET.e 433 5197 1683) (ET.n (ET.e 17 5407 1610) (ET.e 89 5519 1573))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 107 5779 1490) (ET.e 163 5869 1463)) (ET.n (ET.e 19 6043 1416) (ET.e 1033 6199 1374))) (ET.n (ET.n (ET.e 67 6299 1349) (ET.e 7 6427 1317)) (ET.n (ET.e 7 6637 1268) (ET.n (ET.e 283 6793 1234) (ET.e 7 6917 1208))))) (ET.n (ET.n (ET.n (ET.e 19 7069 1177) (ET.e 67 7237 1144)) (ET.n (ET.e 7 7393 1116) (ET.e 7 7547 1088))) (ET.n (ET.n (ET.e 19 7639 1072) (ET.e 59 7789 1048)) (ET.n (ET.e 59 7907 1028) (ET.n (ET.e 19 8209 981) (ET.e 37 8363 960)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 8467 945) (ET.e 19 8627 923)) (ET.n (ET.e 7 8863 893) (ET.e 13 9049 869))) (ET.n (ET.n (ET.e 107 9203 851) (ET.e 1567 9403 827)) (ET.n (ET.e 1187 9497 817) (ET.n (ET.e 67 9649 801) (ET.e 1229 9833 781))))) (ET.n (ET.n (ET.n (ET.e 7 10067 758) (ET.e 19 10223 742)) (ET.n (ET.e 7 10333 732) (ET.n (ET.e 97 10477 719) (ET.e 7 10627 705)))) (ET.n (ET.n (ET.e 5399 10799 690) (ET.e 83 10957 677)) (ET.n (ET.e 7 11117 663) (ET.n (ET.e 1409 11273 651) (ET.e 89 11393 642)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 11579 628) (ET.e 7 11719 617)) (ET.n (ET.e 17 11867 607) (ET.e 17 11969 600))) (ET.n (ET.n (ET.e 2027 12163 586) (ET.e 107 12413 570)) (ET.n (ET.e 523 12553 561) (ET.n (ET.e 193 12739 549) (ET.e 23 12973 535))))) (ET.n (ET.n (ET.n (ET.e 17 13159 524) (ET.e 13 13313 515)) (ET.n (ET.e 563 13513 504) (ET.e 163 13693 494))) (ET.n (ET.n (ET.e 383 13789 488) (ET.e 37 13913 482)) (ET.n (ET.e 13 14249 465) (ET.n (ET.e 233 14447 455) (ET.e 809 14563 450)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2447 14683 444) (ET.e 23 14813 438)) (ET.n (ET.e 227 14983 431) (ET.e 2543 15259 418))) (ET.n (ET.n (ET.e 1279 15349 414) (ET.e 19 15619 403)) (ET.n (ET.e 13 15887 392) (ET.n (ET.e 83 16103 384) (ET.e 199 16319 376))))) (ET.n (ET.n (ET.n (ET.e 8273 16547 366) (ET.e 17 16729 360)) (ET.n (ET.e 23 16883 355) (ET.n (ET.e 19 17063 348) (ET.e 13 17239 342)))) (ET.n (ET.n (ET.e 1087 17393 337) (ET.e 37 17539 332)) (ET.n (ET.e 739 17737 326) (ET.n (ET.e 37 17909 319) (ET.e 4519 18077 314))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 23 18217 310) (ET.e 37 18427 304)) (ET.n (ET.e 283 18679 296) (ET.e 17 18973 288))) (ET.n (ET.n (ET.e 3203 19219 281) (ET.e 13 19423 276)) (ET.n (ET.e 19 19609 270) (ET.n (ET.e 13 19813 265) (ET.e 17 19993 261))))) (ET.n (ET.n (ET.n (ET.e 1439 20147 257) (ET.e 13 20333 253)) (ET.n (ET.e 59 20533 247) (ET.n (ET.e 17 20707 243) (ET.e 1487 20819 240)))) (ET.n (ET.n (ET.e 23 21023 236) (ET.e 3547 21283 229)) (ET.n (ET.e 1783 21397 227) (ET.n (ET.e 17 21557 223) (ET.e 13 21737 220)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 13 21893 216) (ET.e 89 22073 213)) (ET.n (ET.e 5557 22229 209) (ET.e 233 22369 206))) (ET.n (ET.n (ET.e 59 22657 200) (ET.e 19 22877 196)) (ET.n (ET.e 17 23053 193) (ET.n (ET.e 107 23327 187) (ET.e 163 23473 184))))) (ET.n (ET.n (ET.n (ET.e 97 23669 181) (ET.e 5953 23813 178)) (ET.n (ET.e 2999 23993 175) (ET.n (ET.e 367 24223 170) (ET.e 2039 24469 166)))) (ET.n (ET.n (ET.e 13 24649 163) (ET.e 4157 24943 159)) (ET.n (ET.e 37 25087 157) (ET.n (ET.e 13 25273 153) (ET.e 19 25423 150))))))))
private def etCase2_6 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 113 86267) (ET.e 7 197 49424)) (ET.n (ET.e 13 313 31051) (ET.e 13 443 21900))) (ET.n (ET.n (ET.e 13 599 16152) (ET.e 13 677 14267)) (ET.n (ET.e 23 829 11624) (ET.n (ET.e 7 967 9938) (ET.e 7 1093 8774))))) (ET.n (ET.n (ET.n (ET.e 7 1289 7410) (ET.e 13 1483 6415)) (ET.n (ET.e 7 1597 5945) (ET.e 7 1709 5544))) (ET.n (ET.n (ET.e 13 1873 5039) (ET.e 37 1999 4711)) (ET.n (ET.e 89 2137 4392) (ET.n (ET.e 7 2297 4074) (ET.e 109 2399 3893)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 2633 3527) (ET.e 1409 2819 3283)) (ET.n (ET.e 13 2939 3137) (ET.e 193 3089 2976))) (ET.n (ET.n (ET.e 19 3307 2765) (ET.e 13 3407 2678)) (ET.n (ET.e 7 3613 2515) (ET.n (ET.e 7 3767 2401) (ET.e 37 3923 2298))))) (ET.n (ET.n (ET.n (ET.e 2039 4079 2203) (ET.e 19 4219 2124)) (ET.n (ET.e 7 4397 2027) (ET.n (ET.e 7 4523 1965) (ET.e 73 4673 1896)))) (ET.n (ET.n (ET.e 19 4903 1795) (ET.e 23 5107 1716)) (ET.n (ET.e 7 5209 1678) (ET.n (ET.e 7 5419 1606) (ET.e 7 5573 1553))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 5783 1489) (ET.e 67 5897 1456)) (ET.n (ET.e 3023 6047 1415) (ET.e 7 6203 1373))) (ET.n (ET.n (ET.e 109 6323 1342) (ET.e 13 6449 1312)) (ET.n (ET.e 1663 6653 1265) (ET.n (ET.e 19 6803 1232) (ET.e 23 6947 1201))))) (ET.n (ET.n (ET.n (ET.e 3539 7079 1175) (ET.e 17 7243 1143)) (ET.n (ET.e 929 7433 1109) (ET.e 17 7549 1087))) (ET.n (ET.n (ET.e 7 7673 1066) (ET.e 487 7793 1047)) (ET.n (ET.e 37 7919 1026) (ET.n (ET.e 7 8219 980) (ET.e 523 8369 959)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 8513 939) (ET.e 1453 8719 911)) (ET.n (ET.e 13 8867 892) (ET.e 7 9059 868))) (ET.n (ET.n (ET.e 7 9227 848) (ET.e 13 9413 826)) (ET.n (ET.e 19 9539 813) (ET.n (ET.e 59 9677 798) (ET.e 4919 9839 780))))) (ET.n (ET.n (ET.n (ET.e 839 10069 758) (ET.e 569 10243 740)) (ET.n (ET.e 17 10337 732) (ET.n (ET.e 7 10487 718) (ET.e 37 10657 702)))) (ET.n (ET.n (ET.e 7 10837 687) (ET.e 13 10973 676)) (ET.n (ET.e 17 11119 663) (ET.n (ET.e 5639 11279 651) (ET.e 1907 11443 638)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 11593 626) (ET.e 19 11743 616)) (ET.n (ET.e 7 11887 606) (ET.e 13 11987 599))) (ET.n (ET.n (ET.e 3049 12197 584) (ET.e 7 12433 569)) (ET.n (ET.e 233 12583 559) (ET.n (ET.e 23 12743 548) (ET.e 7 12979 534))))) (ET.n (ET.n (ET.n (ET.e 13 13183 523) (ET.e 13 13339 513)) (ET.n (ET.e 17 13567 501) (ET.e 107 13697 494))) (ET.n (ET.n (ET.e 13 13807 487) (ET.e 13 13963 479)) (ET.n (ET.e 59 14279 464) (ET.n (ET.e 19 14479 454) (ET.e 19 14593 448)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7349 14699 443) (ET.e 353 14827 438)) (ET.n (ET.e 3769 15077 426) (ET.e 13 15263 418))) (ET.n (ET.n (ET.e 1097 15359 414) (ET.e 7823 15647 402)) (ET.n (ET.e 13 15913 391) (ET.n (ET.e 733 16127 383) (ET.e 67 16349 374))))) (ET.n (ET.n (ET.n (ET.e 2069 16553 366) (ET.e 19 16759 359)) (ET.n (ET.e 13 16927 353) (ET.n (ET.e 1423 17077 348) (ET.e 13 17317 339)))) (ET.n (ET.n (ET.e 8699 17399 336) (ET.e 23 17573 331)) (ET.n (ET.e 19 17747 325) (ET.n (ET.e 83 17929 319) (ET.e 17 18089 314))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 18253 309) (ET.e 769 18457 303)) (ET.n (ET.e 109 18749 294) (ET.e 97 19013 287))) (ET.n (ET.n (ET.e 13 19267 280) (ET.e 19 19457 275)) (ET.n (ET.e 17 19687 268) (ET.n (ET.e 367 19819 265) (ET.e 1669 20029 260))))) (ET.n (ET.n (ET.n (ET.e 23 20149 257) (ET.e 727 20357 251)) (ET.n (ET.e 23 20563 246) (ET.n (ET.e 3457 20743 242) (ET.e 13 20879 239)))) (ET.n (ET.n (ET.e 173 21107 234) (ET.e 37 21313 228)) (ET.n (ET.e 19 21433 226) (ET.n (ET.e 3593 21559 223) (ET.e 3623 21739 219)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 23 21943 215) (ET.e 19 22079 213)) (ET.n (ET.e 227 22247 208) (ET.e 509 22397 205))) (ET.n (ET.n (ET.e 17 22679 200) (ET.e 13 22907 196)) (ET.n (ET.e 13 23063 193) (ET.n (ET.e 19 23333 187) (ET.e 89 23497 184))))) (ET.n (ET.n (ET.n (ET.e 13 23687 181) (ET.e 19 23827 178)) (ET.n (ET.e 13 23999 175) (ET.n (ET.e 23 24289 169) (ET.e 19 24473 166)))) (ET.n (ET.n (ET.e 199 24677 163) (ET.e 3119 24953 159)) (ET.n (ET.e 13 25117 156) (ET.n (ET.e 12653 25307 152) (ET.e 23 25439 150))))))))
private def etCase2_7 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 127 76746) (ET.e 37 223 43647)) (ET.n (ET.e 7 337 28830) (ET.e 7 449 21606))) (ET.n (ET.n (ET.e 17 613 15780) (ET.e 59 709 13616)) (ET.n (ET.e 107 857 11239) (ET.n (ET.e 83 997 9634) (ET.e 19 1103 8693))))) (ET.n (ET.n (ET.n (ET.e 7 1303 7329) (ET.e 373 1493 6371)) (ET.n (ET.e 73 1607 5907) (ET.e 7 1723 5493))) (ET.n (ET.n (ET.e 7 1877 5028) (ET.e 7 2003 4701)) (ET.n (ET.e 7 2143 4379) (ET.n (ET.e 577 2309 4051) (ET.e 7 2423 3853)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 2647 3508) (ET.e 59 2833 3266)) (ET.n (ET.e 739 2957 3117) (ET.e 7 3109 2956))) (ET.n (ET.n (ET.e 23 3313 2759) (ET.e 853 3413 2673)) (ET.n (ET.e 607 3643 2493) (ET.n (ET.e 13 3797 2381) (ET.e 73 3943 2286))))) (ET.n (ET.n (ET.n (ET.e 683 4099 2192) (ET.e 7 4229 2118)) (ET.n (ET.e 19 4409 2021) (ET.n (ET.e 2273 4547 1954) (ET.e 787 4723 1874)))) (ET.n (ET.n (ET.e 7 4943 1779) (ET.e 853 5119 1711)) (ET.n (ET.e 13 5227 1672) (ET.n (ET.e 907 5443 1598) (ET.e 7 5657 1527))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 2903 5807 1481) (ET.e 13 5903 1454)) (ET.n (ET.e 17 6053 1412) (ET.e 7 6217 1369))) (ET.n (ET.n (ET.e 7 6329 1341) (ET.e 7 6469 1307)) (ET.n (ET.e 7 6679 1259) (ET.n (ET.e 569 6829 1227) (ET.e 193 6949 1201))))) (ET.n (ET.n (ET.n (ET.e 67 7103 1171) (ET.e 3623 7247 1142)) (ET.n (ET.e 233 7457 1104) (ET.e 3779 7559 1086))) (ET.n (ET.n (ET.e 7 7687 1064) (ET.e 977 7817 1043)) (ET.n (ET.e 1987 7949 1021) (ET.n (ET.e 7 8233 978) (ET.e 349 8377 958)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 7 8527 937) (ET.e 7 8737 909)) (ET.n (ET.e 13 8893 889) (ET.e 37 9103 863))) (ET.n (ET.n (ET.e 13 9257 845) (ET.e 17 9419 826)) (ET.n (ET.e 37 9547 812) (ET.n (ET.e 7 9689 797) (ET.e 7 9857 779))))) (ET.n (ET.n (ET.n (ET.e 5039 10079 757) (ET.e 109 10247 740)) (ET.n (ET.e 863 10357 730) (ET.n (ET.e 73 10513 716) (ET.e 5333 10667 701)))) (ET.n (ET.n (ET.e 17 10847 686) (ET.e 37 11027 672)) (ET.n (ET.e 929 11149 661) (ET.n (ET.e 19 11287 650) (ET.e 59 11447 638)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 11597 626) (ET.e 23 11777 613)) (ET.n (ET.e 1487 11897 605) (ET.e 23 12007 597))) (ET.n (ET.n (ET.e 6113 12227 582) (ET.e 173 12457 567)) (ET.n (ET.e 1049 12589 559) (ET.n (ET.e 7 12769 547) (ET.e 7 13007 533))))) (ET.n (ET.n (ET.n (ET.e 19 13187 523) (ET.e 163 13367 512)) (ET.n (ET.e 1697 13577 500) (ET.e 23 13709 493))) (ET.n (ET.n (ET.e 3457 13829 486) (ET.e 6983 13967 479)) (ET.n (ET.e 397 14293 463) (ET.n (ET.e 2417 14503 452) (ET.e 23 14629 447)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 13 14717 443) (ET.e 59 14869 436)) (ET.n (ET.e 13 15107 425) (ET.e 19 15277 417))) (ET.n (ET.n (ET.e 83 15439 411) (ET.e 163 15649 402)) (ET.n (ET.e 19 15923 390) (ET.n (ET.e 8069 16139 382) (ET.e 19 16417 371))))) (ET.n (ET.n (ET.n (ET.e 2767 16603 364) (ET.e 17 16763 359)) (ET.n (ET.e 73 16937 353) (ET.n (ET.e 83 17099 347) (ET.e 8663 17327 339)))) (ET.n (ET.n (ET.e 2903 17419 336) (ET.e 17 17579 331)) (ET.n (ET.e 17 17749 325) (ET.n (ET.e 67 17957 318) (ET.e 13 18097 314))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 163 18257 309) (ET.e 23 18493 302)) (ET.n (ET.e 17 18769 294) (ET.e 227 19069 285))) (ET.n (ET.n (ET.e 73 19273 280) (ET.e 37 19463 275)) (ET.n (ET.e 67 19699 268) (ET.n (ET.e 19 19913 263) (ET.e 13 20047 259))))) (ET.n (ET.n (ET.n (ET.e 13 20177 256) (ET.e 13 20359 251)) (ET.n (ET.e 13 20567 246) (ET.n (ET.e 23 20747 242) (ET.e 59 20887 239)))) (ET.n (ET.n (ET.e 13 21139 233) (ET.e 73 21317 228)) (ET.n (ET.e 199 21493 225) (ET.n (ET.e 109 21583 223) (ET.e 37 21757 219)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 67 21977 215) (ET.e 263 22093 212)) (ET.n (ET.e 359 22259 208) (ET.e 13 22543 202))) (ET.n (ET.n (ET.e 2837 22697 200) (ET.e 89 22963 195)) (ET.n (ET.e 17 23087 192) (ET.n (ET.e 23 23369 186) (ET.e 13 23557 183))))) (ET.n (ET.n (ET.n (ET.e 59 23719 180) (ET.e 13 23843 178)) (ET.n (ET.e 4007 24043 174) (ET.n (ET.e 6079 24317 169) (ET.e 557 24509 166)))) (ET.n (ET.n (ET.e 89 24743 162) (ET.e 19 24967 158)) (ET.n (ET.e 17 25127 156) (ET.n (ET.e 19 25309 152) (ET.e 37 25457 150))))))))
private def etCase2 : ET :=
  ET.n (ET.n (ET.n etCase2_0 etCase2_1) (ET.n etCase2_2 etCase2_3)) (ET.n (ET.n etCase2_4 etCase2_5) (ET.n etCase2_6 etCase2_7))

private def etCase3_0 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 11 23 424283) (ET.n (ET.e 11 89 109578) (ET.e 19 191 50980))) (ET.n (ET.e 47 283 34368) (ET.n (ET.e 11 353 27517) (ET.e 11 419 23162)))) (ET.n (ET.n (ET.e 7 491 19736) (ET.n (ET.e 101 607 15938) (ET.e 11 661 14624))) (ET.n (ET.e 41 739 13058) (ET.n (ET.e 107 857 11239) (ET.e 17 919 10465))))) (ET.n (ET.n (ET.n (ET.e 509 1019 9423) (ET.n (ET.e 19 1103 8693) (ET.e 101 1213 7885))) (ET.n (ET.e 13 1301 7340) (ET.n (ET.e 179 1433 6644) (ET.e 17 1531 6208)))) (ET.n (ET.n (ET.e 271 1627 5832) (ET.n (ET.e 97 1747 5415) (ET.e 17 1871 5045))) (ET.n (ET.e 499 1997 4716) (ET.n (ET.e 13 2081 4515) (ET.e 19 2243 4176)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 2357 3965) (ET.n (ET.e 1229 2459 3790) (ET.e 163 2609 3561))) (ET.n (ET.e 31 2729 3397) (ET.n (ET.e 19 2851 3244) (ET.e 41 2953 3122)))) (ET.n (ET.n (ET.e 17 3163 2902) (ET.n (ET.e 37 3257 2813) (ET.e 73 3359 2719))) (ET.n (ET.e 349 3491 2609) (ET.n (ET.e 101 3637 2497) (ET.e 13 3797 2381))))) (ET.n (ET.n (ET.n (ET.e 17 3911 2306) (ET.n (ET.e 509 4073 2207) (ET.e 47 4231 2117))) (ET.n (ET.e 37 4441 2005) (ET.n (ET.e 19 4561 1947) (ET.e 73 4673 1896)))) (ET.n (ET.n (ET.e 401 4813 1835) (ET.n (ET.e 13 4993 1759) (ET.e 17 5101 1718))) (ET.n (ET.n (ET.e 31 5209 1678) (ET.e 887 5323 1638)) (ET.n (ET.e 151 5437 1600) (ET.e 13 5591 1547))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 41 5741 1502) (ET.n (ET.e 17 5849 1469) (ET.e 31 5953 1440))) (ET.n (ET.e 1013 6079 1405) (ET.n (ET.e 1033 6199 1374) (ET.e 47 6299 1349)))) (ET.n (ET.n (ET.e 17 6427 1317) (ET.n (ET.e 47 6581 1282) (ET.e 97 6791 1235))) (ET.n (ET.e 1151 6907 1210) (ET.n (ET.e 17 7039 1183) (ET.e 1201 7207 1150))))) (ET.n (ET.n (ET.n (ET.e 13 7307 1131) (ET.n (ET.e 19 7487 1099) (ET.e 947 7577 1083))) (ET.n (ET.e 769 7691 1064) (ET.n (ET.e 487 7793 1047) (ET.e 59 7907 1028)))) (ET.n (ET.n (ET.e 61 8053 1005) (ET.n (ET.e 17 8161 989) (ET.e 17 8263 974))) (ET.n (ET.e 37 8363 960) (ET.n (ET.e 17 8467 945) (ET.e 19 8627 923)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 1451 8707 912) (ET.n (ET.e 4391 8783 903) (ET.e 179 8951 881))) (ET.n (ET.e 13 9049 869) (ET.n (ET.e 73 9199 851) (ET.e 19 9311 839)))) (ET.n (ET.n (ET.e 13 9439 322) (ET.n (ET.e 19 9539 813) (ET.e 811 9733 792))) (ET.n (ET.e 1229 9833 781) (ET.n (ET.e 829 9949 770) (ET.e 17 10099 755))))) (ET.n (ET.n (ET.n (ET.e 47 10247 740) (ET.n (ET.e 401 10427 724) (ET.e 587 10567 711))) (ET.n (ET.e 59 10739 695) (ET.n (ET.e 101 10909 681) (ET.e 263 11047 670)))) (ET.n (ET.n (ET.e 797 11159 660) (ET.n (ET.e 19 11287 650) (ET.e 5711 11423 640))) (ET.n (ET.n (ET.e 17 11663 621) (ET.e 151 11779 613)) (ET.n (ET.e 19 11933 602) (ET.e 251 12049 595)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 37 12211 583) (ET.n (ET.e 6173 12347 574) (ET.e 173 12457 567))) (ET.n (ET.e 233 12583 559) (ET.n (ET.e 193 12739 549) (ET.e 107 12841 543)))) (ET.n (ET.n (ET.e 929 13007 533) (ET.n (ET.e 263 13151 525) (ET.e 31 13331 514))) (ET.n (ET.e 17 13499 505) (ET.n (ET.e 853 13649 497) (ET.e 2293 13759 491))))) (ET.n (ET.n (ET.n (ET.e 769 13843 486) (ET.n (ET.e 6983 13967 479) (ET.e 17 14111 472))) (ET.n (ET.e 1193 14317 462) (ET.n (ET.e 37 14431 456) (ET.e 1459 14591 448)))) (ET.n (ET.n (ET.e 2447 14683 444) (ET.n (ET.e 19 14821 438) (ET.e 47 14947 432))) (ET.n (ET.e 151 15101 425) (ET.n (ET.e 17 15233 419) (ET.e 7673 15347 414)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 1291 15493 408) (ET.n (ET.e 17 15641 403) (ET.e 31 15749 397))) (ET.n (ET.e 2657 15943 390) (ET.n (ET.e 41 16073 385) (ET.e 19 16189 380)))) (ET.n (ET.n (ET.e 19 16417 371) (ET.n (ET.e 1381 16573 365) (ET.e 17 16729 360))) (ET.n (ET.e 17 16831 356) (ET.n (ET.e 73 16937 353) (ET.e 4273 17093 347))))) (ET.n (ET.n (ET.n (ET.e 31 17299 340) (ET.n (ET.e 17 17443 335) (ET.e 31 17609 330))) (ET.n (ET.e 887 17741 326) (ET.n (ET.e 991 17839 323) (ET.e 17 17987 317)))) (ET.n (ET.n (ET.e 19 18127 313) (ET.n (ET.e 3037 18223 310) (ET.e 31 18353 306))) (ET.n (ET.n (ET.e 179 18617 299) (ET.e 37 18797 293)) (ET.n (ET.e 19 19001 287) (ET.e 139 19183 282))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 73 19273 280) (ET.n (ET.e 1619 19429 276) (ET.e 181 19549 272))) (ET.n (ET.e 17 19687 268) (ET.n (ET.e 31 19841 264) (ET.e 47 20023 260)))) (ET.n (ET.n (ET.e 41 20173 256) (ET.n (ET.e 563 20269 254) (ET.e 227 20431 249))) (ET.n (ET.e 10313 20627 245) (ET.n (ET.e 1151 20719 243) (ET.e 577 20773 241))))) (ET.n (ET.n (ET.n (ET.e 109 20929 238) (ET.n (ET.e 31 21019 236) (ET.e 241 21209 232))) (ET.n (ET.e 1523 21323 228) (ET.n (ET.e 139 21407 226) (ET.e 17 21523 224)))) (ET.n (ET.n (ET.e 2161 21611 222) (ET.n (ET.e 59 21713 220) (ET.e 173 21799 218))) (ET.n (ET.n (ET.e 1823 21877 217) (ET.e 2203 22031 214)) (ET.n (ET.e 5527 22109 212) (ET.e 17 22271 208)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2239 22391 205) (ET.n (ET.e 1879 22549 202) (ET.e 59 22657 200))) (ET.n (ET.e 1423 22769 198) (ET.n (ET.e 31 22879 196) (ET.e 59 23011 194)))) (ET.n (ET.n (ET.e 577 23081 192) (ET.n (ET.e 829 23213 189) (ET.e 167 23381 186))) (ET.n (ET.e 151 23557 183) (ET.n (ET.e 31 23623 182) (ET.e 59 23719 180))))) (ET.n (ET.n (ET.n (ET.e 11909 23819 178) (ET.n (ET.e 797 23911 177) (ET.e 4003 24019 175))) (ET.n (ET.e 41 24109 173) (ET.n (ET.e 12143 24287 169) (ET.e 37 24421 167)))) (ET.n (ET.n (ET.e 61 24523 165) (ET.n (ET.e 41 24683 163) (ET.e 17 24821 161))) (ET.n (ET.n (ET.e 3119 24953 159) (ET.e 1567 25073 157)) (ET.n (ET.e 59 25253 154) (ET.e 19 25423 150))))))))
private def etCase3_1 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 29 336487) (ET.n (ET.e 17 103 94653) (ET.e 7 197 49424))) (ET.n (ET.e 73 293 33191) (ET.n (ET.e 179 359 27055) (ET.e 7 421 23051)))) (ET.n (ET.n (ET.e 251 503 19262) (ET.n (ET.e 17 613 15780) (ET.e 7 673 14353))) (ET.n (ET.e 7 743 12986) (ET.n (ET.e 11 859 11213) (ET.e 13 937 10261))))) (ET.n (ET.n (ET.n (ET.e 17 1021 9404) (ET.n (ET.e 277 1109 8645) (ET.e 19 1217 7858))) (ET.n (ET.e 31 1303 7329) (ET.n (ET.e 719 1439 6616) (ET.e 257 1543 6159)))) (ET.n (ET.n (ET.e 277 1663 5702) (ET.n (ET.e 73 1753 5396) (ET.e 13 1873 5039))) (ET.n (ET.e 37 1999 4711) (ET.n (ET.e 1049 2099 4474) (ET.e 19 2281 4103)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 2381 3924) (ET.n (ET.e 619 2477 3761) (ET.e 109 2617 3550))) (ET.n (ET.e 13 2731 3394) (ET.n (ET.e 17 2857 3237) (ET.e 19 3041 3026)))) (ET.n (ET.n (ET.e 1583 3167 2898) (ET.n (ET.e 181 3259 2811) (ET.e 13 3407 2678))) (ET.n (ET.e 13 3511 2593) (ET.n (ET.e 31 3659 2481) (ET.e 13 3823 2363))))) (ET.n (ET.n (ET.n (ET.e 37 3923 2298) (ET.n (ET.e 2039 4079 2203) (ET.e 101 4243 2111))) (ET.n (ET.e 13 4447 2002) (ET.n (ET.e 17 4591 1933) (ET.e 59 4721 1875)))) (ET.n (ET.n (ET.e 487 4871 1808) (ET.n (ET.e 17 4999 1757) (ET.e 37 5107 1716))) (ET.n (ET.n (ET.e 13 5227 1672) (ET.e 31 5333 1635)) (ET.n (ET.e 17 5441 1598) (ET.e 47 5641 1532))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 479 5749 1499) (ET.n (ET.e 13 5851 1469) (ET.e 13 5981 1432))) (ET.n (ET.e 61 6101 1399) (ET.n (ET.e 37 6217 1369) (ET.e 109 6323 1342)))) (ET.n (ET.n (ET.e 13 6449 1312) (ET.n (ET.e 37 6661 1263) (ET.e 19 6803 1232))) (ET.n (ET.e 691 6911 1209) (ET.n (ET.e 19 7069 1177) (ET.e 601 7213 1149))))) (ET.n (ET.n (ET.n (ET.e 61 7321 1129) (ET.n (ET.e 13 7489 1099) (ET.e 17 7583 1082))) (ET.n (ET.e 3851 7703 1062) (ET.n (ET.e 19 7829 1041) (ET.e 37 7919 1026)))) (ET.n (ET.n (ET.e 17 8059 1005) (ET.n (ET.e 19 8171 988) (ET.e 13 8269 973))) (ET.n (ET.e 523 8369 959) (ET.n (ET.e 17 8501 941) (ET.e 719 8629 923)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 1453 8719 911) (ET.n (ET.e 163 8803 900) (ET.e 4481 8963 879))) (ET.n (ET.e 101 9091 864) (ET.n (ET.e 107 9203 851) (ET.e 59 9323 837)))) (ET.n (ET.n (ET.e 19 9463 821) (ET.n (ET.e 37 9547 812) (ET.e 541 9739 792))) (ET.n (ET.e 4919 9839 780) (ET.n (ET.e 151 9967 768) (ET.e 17 10133 752))))) (ET.n (ET.n (ET.n (ET.e 233 10253 739) (ET.n (ET.e 163 10433 723) (ET.e 2647 10589 709))) (ET.n (ET.e 31 10789 691) (ET.n (ET.e 1367 10937 679) (ET.e 691 11057 669)))) (ET.n (ET.n (ET.e 31 11161 660) (ET.n (ET.e 269 11299 649) (ET.e 1907 11443 638))) (ET.n (ET.n (ET.e 139 11677 620) (ET.e 59 11801 612)) (ET.n (ET.e 47 11939 602) (ET.e 17 12071 593)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 6113 12227 582) (ET.n (ET.e 1031 12373 572) (ET.e 17 12479 566))) (ET.n (ET.e 1049 12589 559) (ET.n (ET.e 277 12743 548) (ET.e 17 12853 542)))) (ET.n (ET.n (ET.e 271 13009 533) (ET.n (ET.e 17 13159 524) (ET.e 19 13339 513))) (ET.n (ET.e 563 13513 504) (ET.n (ET.e 17 13669 496) (ET.e 983 13763 491))))) (ET.n (ET.n (ET.n (ET.e 41 13859 485) (ET.n (ET.e 3499 13997 478) (ET.e 61 14153 470))) (ET.n (ET.e 179 14321 462) (ET.n (ET.e 401 14437 456) (ET.e 19 14593 448)))) (ET.n (ET.n (ET.e 17 14723 442) (ET.n (ET.e 41 14843 437) (ET.e 3739 14957 432))) (ET.n (ET.e 17 15131 424) (ET.n (ET.e 587 15263 418) (ET.e 1279 15349 414)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 47 15511 408) (ET.n (ET.e 7823 15647 402) (ET.e 7901 15803 395))) (ET.n (ET.e 101 15959 389) (ET.n (ET.e 383 16087 384) (ET.e 541 16231 379)))) (ET.n (ET.n (ET.e 2741 16447 370) (ET.n (ET.e 19 16607 364) (ET.e 31 16741 359))) (ET.n (ET.e 61 16837 356) (ET.n (ET.e 257 16963 352) (ET.e 31 17113 346))))) (ET.n (ET.n (ET.n (ET.e 37 17317 339) (ET.n (ET.e 41 17467 334) (ET.e 1471 17653 328))) (ET.n (ET.e 19 17747 325) (ET.n (ET.e 17 17851 322) (ET.e 19 18013 316)))) (ET.n (ET.n (ET.e 37 18131 313) (ET.n (ET.e 31 18229 310) (ET.e 167 18371 306))) (ET.n (ET.n (ET.e 1867 18671 296) (ET.e 17 18803 293)) (ET.n (ET.e 97 19013 287) (ET.e 97 19207 282))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 193 19301 279) (ET.n (ET.e 19 19457 275) (ET.e 47 19553 272))) (ET.n (ET.e 31 19717 268) (ET.n (ET.e 3313 19879 263) (ET.e 257 20047 259)))) (ET.n (ET.n (ET.e 97 20177 256) (ET.n (ET.e 59 20297 253) (ET.e 73 20441 249))) (ET.n (ET.e 17 20639 244) (ET.n (ET.e 691 20731 242) (ET.e 101 20807 241))))) (ET.n (ET.n (ET.n (ET.e 19 20939 238) (ET.n (ET.e 61 21107 234) (ET.e 101 21211 232))) (ET.n (ET.e 97 21341 228) (ET.n (ET.e 19 21433 226) (ET.e 17 21557 223)))) (ET.n (ET.n (ET.e 1801 21613 222) (ET.n (ET.e 17 21727 220) (ET.e 991 21803 218))) (ET.n (ET.n (ET.e 2741 21929 216) (ET.e 787 22037 213)) (ET.n (ET.e 1229 22123 212) (ET.e 5569 22277 208)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 509 22397 205) (ET.n (ET.e 37 22571 202) (ET.e 17 22679 200))) (ET.n (ET.e 73 22777 198) (ET.n (ET.e 881 22907 196) (ET.e 1151 23021 193)))) (ET.n (ET.n (ET.e 17 23087 192) (ET.n (ET.e 31 23251 188) (ET.e 17 23393 186))) (ET.n (ET.e 19 23561 183) (ET.n (ET.e 11813 23627 182) (ET.e 1187 23741 180))))) (ET.n (ET.n (ET.n (ET.e 19 23827 178) (ET.n (ET.e 1993 23917 177) (ET.e 4007 24043 174))) (ET.n (ET.e 2011 24133 173) (ET.n (ET.e 4051 24307 169) (ET.e 101 24443 167)))) (ET.n (ET.n (ET.e 4091 24547 165) (ET.n (ET.e 823 24691 163) (ET.e 41 24847 160))) (ET.n (ET.n (ET.e 19 24967 158) (ET.e 37 25087 157)) (ET.n (ET.e 12641 25283 153) (ET.e 4241 25447 150))))))))
private def etCase3_2 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 43 226892) (ET.n (ET.e 7 113 86267) (ET.e 11 199 48926))) (ET.n (ET.e 17 307 31660) (ET.n (ET.e 61 367 26463) (ET.e 73 439 22101)))) (ET.n (ET.n (ET.e 13 521 18592) (ET.n (ET.e 7 617 15677) (ET.e 13 677 14267))) (ET.n (ET.e 7 757 12743) (ET.n (ET.e 431 863 11154) (ET.e 47 941 10216))))) (ET.n (ET.n (ET.n (ET.e 173 1039 9238) (ET.n (ET.e 31 1117 8576) (ET.e 13 1223 7819))) (ET.n (ET.e 13 1327 7193) (ET.n (ET.e 241 1447 6578) (ET.e 97 1553 6118)))) (ET.n (ET.n (ET.e 17 1667 5688) (ET.n (ET.e 37 1777 5321) (ET.e 59 1889 4995))) (ET.n (ET.e 13 2003 4701) (ET.n (ET.e 19 2129 4409) (ET.e 41 2297 4074)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 13 2393 3903) (ET.n (ET.e 139 2503 3720) (ET.e 47 2633 3527))) (ET.n (ET.e 461 2767 3348) (ET.n (ET.e 13 2861 3232) (ET.e 17 3061 3005)))) (ET.n (ET.n (ET.e 59 3187 2879) (ET.n (ET.e 109 3271 2800) (ET.e 853 3413 2673))) (ET.n (ET.e 41 3527 2581) (ET.n (ET.e 17 3673 2471) (ET.e 479 3833 2357))))) (ET.n (ET.n (ET.n (ET.e 73 3943 2286) (ET.n (ET.e 31 4093 2195) (ET.e 61 4271 2096))) (ET.n (ET.e 97 4463 1994) (ET.n (ET.e 383 4597 1931) (ET.e 787 4723 1874)))) (ET.n (ET.n (ET.e 13 4889 1801) (ET.n (ET.e 41 5003 1755) (ET.e 853 5119 1711))) (ET.n (ET.n (ET.e 523 5231 1670) (ET.e 107 5351 1628)) (ET.n (ET.e 227 5449 1596) (ET.e 101 5657 1527))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 107 5779 1490) (ET.n (ET.e 61 5857 1467) (ET.e 41 5987 1431))) (ET.n (ET.e 17 6121 1394) (ET.n (ET.e 173 6229 1366) (ET.e 151 6343 1337)))) (ET.n (ET.n (ET.e 59 6491 1302) (ET.n (ET.e 139 6673 1260) (ET.e 569 6829 1227))) (ET.n (ET.e 13 6917 1208) (ET.n (ET.e 509 7127 1166) (ET.e 401 7219 1147))))) (ET.n (ET.n (ET.n (ET.e 13 7333 1126) (ET.n (ET.e 163 7499 1097) (ET.e 271 7589 1081))) (ET.n (ET.e 13 7723 1058) (ET.n (ET.e 13 7853 1036) (ET.e 1321 7927 1025)))) (ET.n (ET.n (ET.e 2017 8069 1003) (ET.n (ET.e 47 8179 987) (ET.e 47 8273 972))) (ET.n (ET.e 349 8377 958) (ET.n (ET.e 19 8513 939) (ET.e 61 8663 918)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 97 8731 909) (ET.n (ET.e 17 8807 900) (ET.e 19 8969 879))) (ET.n (ET.e 37 9103 863) (ET.n (ET.e 1151 9209 850) (ET.e 173 9343 834)))) (ET.n (ET.n (ET.e 37 9473 820) (ET.n (ET.e 4793 9587 808) (ET.e 2437 9749 790))) (ET.n (ET.e 31 9859 778) (ET.n (ET.e 277 9973 767) (ET.e 37 10139 751))))) (ET.n (ET.n (ET.n (ET.e 59 10267 738) (ET.n (ET.e 1307 10457 721) (ET.e 17 10609 707))) (ET.n (ET.e 5399 10799 690) (ET.n (ET.e 1823 10939 679) (ET.e 19 11059 669)))) (ET.n (ET.n (ET.e 19 11173 659) (ET.n (ET.e 41 11317 648) (ET.e 59 11447 638))) (ET.n (ET.n (ET.e 73 11681 620) (ET.e 73 11827 610)) (ET.n (ET.e 1993 11959 601) (ET.e 31 12091 592)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 12241 581) (ET.n (ET.e 17 12377 572) (ET.e 19 12503 564))) (ET.n (ET.e 97 12611 557) (ET.n (ET.e 19 12769 547) (ET.e 179 12889 540)))) (ET.n (ET.n (ET.e 181 13033 531) (ET.n (ET.e 61 13177 523) (ET.e 41 13367 512))) (ET.n (ET.e 47 13537 502) (ET.n (ET.e 19 13681 495) (ET.e 383 13789 488))))) (ET.n (ET.n (ET.n (ET.e 17 13873 484) (ET.n (ET.e 2333 13999 478) (ET.e 7079 14159 470))) (ET.n (ET.e 31 14323 462) (ET.n (ET.e 31 14447 455) (ET.e 17 14621 447)))) (ET.n (ET.n (ET.e 73 14747 441) (ET.n (ET.e 59 14869 436) (ET.e 227 14983 431))) (ET.n (ET.e 541 15149 423) (ET.n (ET.e 509 15271 418) (ET.e 1097 15359 414)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 37 15541 407) (ET.n (ET.e 163 15649 402) (ET.e 19 15809 395))) (ET.n (ET.e 41 15991 388) (ET.n (ET.e 1609 16091 384) (ET.e 17 16253 378)))) (ET.n (ET.n (ET.e 47 16451 370) (ET.n (ET.e 1187 16619 364) (ET.e 19 16759 359))) (ET.n (ET.e 401 16843 356) (ET.n (ET.e 19 16987 351) (ET.e 17 17137 345))))) (ET.n (ET.n (ET.n (ET.e 433 17321 339) (ET.n (ET.e 17 17477 334) (ET.e 2207 17657 328))) (ET.n (ET.e 17 17749 325) (ET.n (ET.e 1789 17891 320) (ET.e 41 18041 315)))) (ET.n (ET.n (ET.e 47 18143 312) (ET.n (ET.e 73 18251 309) (ET.e 73 18397 305))) (ET.n (ET.n (ET.e 17 18701 295) (ET.e 17 18871 291)) (ET.n (ET.e 173 19031 286) (ET.e 17 19211 282))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 1609 19309 279) (ET.n (ET.e 37 19463 275) (ET.e 19 19571 271))) (ET.n (ET.e 1409 19727 267) (ET.n (ET.e 17 19891 263) (ET.e 401 20051 259)))) (ET.n (ET.n (ET.e 10091 20183 256) (ET.n (ET.e 17 20333 253) (ET.e 5113 20453 249))) (ET.n (ET.e 59 20651 244) (ET.n (ET.e 3457 20743 242) (ET.e 17 20809 241))))) (ET.n (ET.n (ET.n (ET.e 499 20959 237) (ET.n (ET.e 271 21139 233) (ET.e 1061 21221 231))) (ET.n (ET.e 17 21353 228) (ET.n (ET.e 61 21473 225) (ET.e 3593 21559 223)))) (ET.n (ET.n (ET.e 193 21617 222) (ET.n (ET.e 19 21737 220) (ET.e 47 21809 218))) (ET.n (ET.n (ET.e 61 21961 215) (ET.e 3677 22063 213)) (ET.n (ET.e 461 22129 212) (ET.e 47 22279 208)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2801 22409 205) (ET.n (ET.e 19 22573 202) (ET.e 2269 22691 200))) (ET.n (ET.e 11393 22787 198) (ET.n (ET.e 47 22937 195) (ET.e 19 23029 193)))) (ET.n (ET.n (ET.e 11549 23099 192) (ET.n (ET.e 277 23269 188) (ET.e 11699 23399 186))) (ET.n (ET.e 17 23563 183) (ET.n (ET.e 179 23629 182) (ET.e 1319 23743 180))))) (ET.n (ET.n (ET.n (ET.e 2383 23831 178) (ET.n (ET.e 997 23929 176) (ET.e 167 24049 174))) (ET.n (ET.e 431 24137 173) (ET.n (ET.e 19 24359 168) (ET.e 2039 24469 166)))) (ET.n (ET.n (ET.e 107 24611 164) (ET.n (ET.e 139 24743 162) (ET.e 1381 24859 160))) (ET.n (ET.n (ET.e 227 24971 158) (ET.e 3137 25097 156)) (ET.n (ET.e 12653 25307 152) (ET.e 101 25453 150))))))))
private def etCase3_3 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 53 184066) (ET.n (ET.e 7 127 76746) (ET.e 7 211 46136))) (ET.n (ET.e 31 311 31251) (ET.n (ET.e 31 373 26035) (ET.e 13 443 21900)))) (ET.n (ET.n (ET.e 7 547 17701) (ET.n (ET.e 7 631 15326) (ET.e 11 683 14140))) (ET.n (ET.e 19 761 12676) (ET.n (ET.e 73 877 10973) (ET.e 7 953 10086))))) (ET.n (ET.n (ET.n (ET.e 7 1051 9131) (ET.n (ET.e 17 1123 8530) (ET.e 41 1231 7767))) (ET.n (ET.e 17 1361 7010) (ET.n (ET.e 37 1481 6424) (ET.e 19 1559 6094)))) (ET.n (ET.n (ET.e 139 1669 5681) (ET.n (ET.e 19 1787 5290) (ET.e 19 1901 4963))) (ET.n (ET.e 1013 2027 4643) (ET.n (ET.e 107 2141 4383) (ET.e 577 2309 4051)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 109 2399 3893) (ET.n (ET.e 47 2539 3665) (ET.e 17 2687 3453))) (ET.n (ET.e 17 2789 3320) (ET.n (ET.e 13 2887 3201) (ET.e 73 3067 2999)))) (ET.n (ET.n (ET.e 1601 3203 2864) (ET.n (ET.e 17 3299 2772) (ET.e 13 3433 2656))) (ET.n (ET.e 61 3539 2571) (ET.n (ET.e 41 3691 2458) (ET.e 641 3847 2348))))) (ET.n (ET.n (ET.n (ET.e 997 3989 2257) (ET.n (ET.e 1033 4133 2172) (ET.e 179 4297 2079))) (ET.n (ET.e 751 4507 1973) (ET.n (ET.e 13 4603 1928) (ET.e 13 4733 1870)))) (ET.n (ET.n (ET.e 19 4903 1795) (ET.n (ET.e 167 5011 1752) (ET.e 31 5147 1701))) (ET.n (ET.n (ET.e 109 5233 1670) (ET.e 269 5381 1618)) (ET.n (ET.e 37 5477 1586) (ET.e 41 5659 1526))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 59 5783 1489) (ET.n (ET.e 163 5869 1463) (ET.e 13 6007 1425))) (ET.n (ET.e 73 6133 1391) (ET.n (ET.e 17 6257 1359) (ET.e 17 6359 1333)))) (ET.n (ET.n (ET.e 163 6521 1295) (ET.n (ET.e 19 6689 1257) (ET.e 61 6833 1226))) (ET.n (ET.e 151 6947 1201) (ET.n (ET.e 13 7151 1161) (ET.e 13 7229 1146))))) (ET.n (ET.n (ET.n (ET.e 167 7349 1124) (ET.n (ET.e 139 7507 1096) (ET.e 181 7603 1078))) (ET.n (ET.e 3863 7727 1058) (ET.n (ET.e 19 7867 1034) (ET.e 31 7937 1023)))) (ET.n (ET.n (ET.e 101 8081 1001) (ET.n (ET.e 13 8191 985) (ET.e 1381 8287 970))) (ET.n (ET.e 233 8389 956) (ET.n (ET.e 97 8537 936) (ET.e 241 8677 916)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 13 8737 909) (ET.n (ET.e 47 8837 896) (ET.e 13 8971 878))) (ET.n (ET.e 13 9127 860) (ET.n (ET.e 461 9221 849) (ET.e 19 9349 833)))) (ET.n (ET.n (ET.e 73 9491 818) (ET.n (ET.e 17 9623 804) (ET.e 19 9767 788))) (ET.n (ET.e 47 9871 777) (ET.n (ET.e 139 10009 764) (ET.e 5081 10163 749))))) (ET.n (ET.n (ET.n (ET.e 107 10273 738) (ET.n (ET.e 97 10477 719) (ET.e 37 10657 702))) (ET.n (ET.e 19 10831 688) (ET.n (ET.e 17 10949 678) (ET.e 41 11071 668)))) (ET.n (ET.n (ET.e 2803 11213 656) (ET.n (ET.e 59 11329 647) (ET.e 31 11471 636))) (ET.n (ET.n (ET.e 487 11689 619) (ET.e 17 11833 609)) (ET.n (ET.e 17 11969 600) (ET.e 73 12119 589)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 6131 12263 579) (ET.n (ET.e 59 12391 571) (ET.e 139 12511 564))) (ET.n (ET.e 6329 12659 553) (ET.n (ET.e 1279 12791 546) (ET.e 1291 12911 538)))) (ET.n (ET.n (ET.e 233 13049 530) (ET.n (ET.e 19 13187 523) (ET.e 17 13397 510))) (ET.n (ET.e 17 13567 501) (ET.n (ET.e 37 13691 494) (ET.e 6899 13799 488))))) (ET.n (ET.n (ET.n (ET.e 257 13879 484) (ET.n (ET.e 17 14009 477) (ET.e 7103 14207 467))) (ET.n (ET.e 19 14327 462) (ET.n (ET.e 241 14461 454) (ET.e 31 14633 446)))) (ET.n (ET.n (ET.e 461 14753 441) (ET.n (ET.e 173 14879 435) (ET.e 139 15013 430))) (ET.n (ET.e 101 15151 423) (ET.n (ET.e 19 15277 417) (ET.e 61 15373 413)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 2593 15559 406) (ET.n (ET.e 1567 15671 401) (ET.e 881 15859 393))) (ET.n (ET.e 151 16007 387) (ET.n (ET.e 97 16103 384) (ET.e 163 16301 376)))) (ET.n (ET.n (ET.e 1373 16477 369) (ET.n (ET.e 4159 16637 363) (ET.e 17 16763 359))) (ET.n (ET.e 241 16871 355) (ET.n (ET.e 59 16993 351) (ET.e 47 17203 343))))) (ET.n (ET.n (ET.n (ET.e 619 17333 339) (ET.n (ET.e 1459 17509 333) (ET.e 109 17659 328))) (ET.n (ET.e 37 17761 325) (ET.n (ET.e 37 17909 319) (ET.e 31 18043 315)))) (ET.n (ET.n (ET.e 349 18149 312) (ET.n (ET.e 163 18257 309) (ET.e 37 18427 304))) (ET.n (ET.n (ET.e 9371 18743 294) (ET.e 31 18911 290)) (ET.n (ET.e 227 19069 285) (ET.e 1601 19213 281))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 179 19333 278) (ET.n (ET.e 31 19469 275) (ET.e 2447 19577 271))) (ET.n (ET.e 139 19739 267) (ET.n (ET.e 19 19913 263) (ET.e 31 20089 258)))) (ET.n (ET.n (ET.e 101 20201 256) (ET.n (ET.e 3391 20347 251) (ET.e 19 20483 248))) (ET.n (ET.e 47 20681 243) (ET.n (ET.e 41 20747 242) (ET.e 1487 20819 240))))) (ET.n (ET.n (ET.n (ET.e 47 20963 237) (ET.n (ET.e 31 21143 233) (ET.e 10613 21227 231))) (ET.n (ET.e 167 21377 227) (ET.n (ET.e 179 21481 225) (ET.e 10781 21563 223)))) (ET.n (ET.n (ET.e 41 21649 221) (ET.n (ET.e 3623 21739 219) (ET.e 101 21817 218))) (ET.n (ET.n (ET.e 41 21977 215) (ET.e 17 22067 213)) (ET.n (ET.e 19 22193 209) (ET.e 59 22303 207)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 22441 204) (ET.n (ET.e 17 22577 202) (ET.e 2837 22697 200))) (ET.n (ET.e 19 22801 198) (ET.n (ET.e 41 22961 195) (ET.e 11519 23039 193)))) (ET.n (ET.n (ET.e 257 23131 191) (ET.n (ET.e 17 23291 188) (ET.e 19 23447 185))) (ET.n (ET.e 11783 23567 183) (ET.n (ET.e 11831 23663 181) (ET.e 31 23747 179))))) (ET.n (ET.n (ET.n (ET.e 1193 23861 178) (ET.n (ET.e 17 23971 176) (ET.e 401 24061 174))) (ET.n (ET.e 19 24169 172) (ET.n (ET.e 2437 24371 168) (ET.e 19 24473 166)))) (ET.n (ET.n (ET.e 17 24617 164) (ET.n (ET.e 269 24749 162) (ET.e 691 24877 160))) (ET.n (ET.n (ET.e 181 24979 158) (ET.e 31 25111 156)) (ET.n (ET.e 19 25309 152) (ET.e 37 25457 150))))))))
private def etCase3_4 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 11 67 145587) (ET.n (ET.e 13 131 74399) (ET.e 37 223 43647))) (ET.n (ET.e 13 313 31051) (ET.n (ET.e 7 379 25620) (ET.e 7 449 21606)))) (ET.n (ET.n (ET.e 139 557 17381) (ET.n (ET.e 107 643 15037) (ET.e 7 701 13773))) (ET.n (ET.e 193 773 12477) (ET.n (ET.e 11 881 1114) (ET.e 7 967 9938))))) (ET.n (ET.n (ET.n (ET.e 59 1063 9026) (ET.n (ET.e 47 1129 8483) (ET.e 13 1249 7653))) (ET.n (ET.e 7 1373 6384) (ET.n (ET.e 13 1483 6415) (ET.e 263 1579 6015)))) (ET.n (ET.n (ET.e 47 1693 5598) (ET.n (ET.e 181 1811 5218) (ET.e 193 1931 4883))) (ET.n (ET.e 13 2029 4639) (ET.n (ET.e 17 2143 4379) (ET.e 167 2339 3997)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 241 2411 3873) (ET.n (ET.e 31 2543 3658) (ET.e 19 2699 3437))) (ET.n (ET.e 31 2791 3317) (ET.n (ET.e 181 2897 3186) (ET.e 19 3079 2986)))) (ET.n (ET.n (ET.e 401 3209 2858) (ET.n (ET.e 19 3307 2765) (ET.e 431 3449 2643))) (ET.n (ET.e 59 3541 2570) (ET.n (ET.e 37 3701 2451) (ET.e 107 3853 2344))))) (ET.n (ET.n (ET.n (ET.e 17 4013 2243) (ET.n (ET.e 173 4153 2161) (ET.e 271 4337 2058))) (ET.n (ET.e 47 4513 1970) (ET.n (ET.e 19 4637 1912) (ET.e 19 4751 1862)))) (ET.n (ET.n (ET.e 17 4931 1784) (ET.n (ET.e 251 5021 1748) (ET.e 41 5167 1693))) (ET.n (ET.n (ET.e 17 5237 1668) (ET.e 2693 5387 1616)) (ET.n (ET.e 2741 5483 1585) (ET.e 13 5669 1523))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 193 5791 1487) (ET.n (ET.e 13 5903 1454) (ET.e 601 6011 1424))) (ET.n (ET.e 37 6143 1388) (ET.n (ET.e 31 6263 1358) (ET.e 1061 6367 1331)))) (ET.n (ET.n (ET.e 17 6529 1293) (ET.n (ET.e 13 6709 1252) (ET.e 19 6841 1224))) (ET.n (ET.e 193 6949 1201) (ET.n (ET.e 1193 7159 1160) (ET.e 17 7243 1143))))) (ET.n (ET.n (ET.n (ET.e 13 7411 1112) (ET.n (ET.e 1879 7517 1093) (ET.e 3803 7607 1078))) (ET.n (ET.e 17 7753 1053) (ET.n (ET.e 41 7873 1033) (ET.e 1987 7949 1021)))) (ET.n (ET.n (ET.e 13 8087 1000) (ET.n (ET.e 19 8209 981) (ET.e 829 8291 970))) (ET.n (ET.e 61 8419 952) (ET.n (ET.e 1423 8539 935) (ET.e 31 8681 916)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 8741 908) (ET.n (ET.e 13 8867 892) (ET.e 19 9007 874))) (ET.n (ET.e 61 9151 857) (ET.n (ET.e 31 9239 847) (ET.e 1567 9403 827)))) (ET.n (ET.n (ET.e 1187 9497 817) (ET.n (ET.e 107 9631 803) (ET.e 37 9769 788))) (ET.n (ET.e 61 9883 776) (ET.n (ET.e 193 10037 761) (ET.e 31 10169 748))))) (ET.n (ET.n (ET.n (ET.e 17 10303 735) (ET.n (ET.e 107 10487 718) (ET.e 1069 10691 699))) (ET.n (ET.e 17 10847 686) (ET.n (ET.e 499 10979 675) (ET.e 241 11087 667)))) (ET.n (ET.n (ET.e 73 11243 654) (ET.n (ET.e 227 11351 645) (ET.e 383 11491 635))) (ET.n (ET.n (ET.e 101 11717 617) (ET.e 17 11867 607)) (ET.n (ET.e 19 11971 600) (ET.e 3037 12149 587)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 31 12277 578) (ET.n (ET.e 31 12401 571) (ET.e 19 12541 562))) (ET.n (ET.e 181 12671 553) (ET.n (ET.e 1601 12809 544) (ET.e 1619 12953 536)))) (ET.n (ET.n (ET.e 109 13081 529) (ET.n (ET.e 59 13217 520) (ET.e 61 13421 509))) (ET.n (ET.e 1697 13577 500) (ET.n (ET.e 163 13693 494) (ET.e 59 13807 487))))) (ET.n (ET.n (ET.n (ET.e 139 13901 483) (ET.n (ET.e 73 14017 477) (ET.e 7121 14243 466))) (ET.n (ET.e 797 14347 461) (ET.n (ET.e 19 14479 454) (ET.e 563 14639 446)))) (ET.n (ET.n (ET.e 47 14759 441) (ET.n (ET.e 19 14897 435) (ET.e 1877 15017 429))) (ET.n (ET.e 3793 15173 422) (ET.n (ET.e 7649 15299 416) (ET.e 31 15377 413)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 139 15569 405) (ET.n (ET.e 7841 15683 401) (ET.e 47 15887 392))) (ET.n (ET.e 167 16033 386) (ET.n (ET.e 179 16111 383) (ET.e 41 16319 376)))) (ET.n (ET.n (ET.e 19 16493 368) (ET.n (ET.e 37 16651 363) (ET.e 109 16787 358))) (ET.n (ET.e 97 16879 355) (ET.n (ET.e 37 17021 350) (ET.e 1229 17207 343))))) (ET.n (ET.n (ET.n (ET.e 17 17341 338) (ET.n (ET.e 19 17519 333) (ET.e 17 17681 328))) (ET.n (ET.e 47 17767 325) (ET.n (ET.e 997 17947 318) (ET.e 47 18049 315)))) (ET.n (ET.n (ET.e 101 18181 311) (ET.n (ET.e 4567 18269 309) (ET.e 41 18451 303))) (ET.n (ET.n (ET.e 109 18749 294) (ET.e 4729 18917 289)) (ET.n (ET.e 3181 19087 285) (ET.e 641 19231 281))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 167 19373 277) (ET.n (ET.e 59 19471 275) (ET.e 9791 19583 271))) (ET.n (ET.e 823 19753 267) (ET.n (ET.e 433 19919 262) (ET.e 47 20117 258)))) (ET.n (ET.n (ET.e 3371 20227 255) (ET.n (ET.e 19 20369 251) (ET.e 61 20497 248))) (ET.n (ET.e 10343 20687 243) (ET.n (ET.e 19 20749 242) (ET.e 73 20879 239))))) (ET.n (ET.n (ET.n (ET.e 1049 20981 237) (ET.n (ET.e 17 21149 233) (ET.e 3547 21283 229))) (ET.n (ET.e 509 21379 227) (ET.n (ET.e 3583 21499 224) (ET.e 31 21577 223)))) (ET.n (ET.n (ET.e 19 21661 221) (ET.n (ET.e 37 21757 219) (ET.e 61 21839 217))) (ET.n (ET.e 47 21997 214) (ET.n (ET.e 31 22073 213) (ET.e 37 22201 209)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 22307 207) (ET.n (ET.e 41 22469 204) (ET.e 5653 22613 201))) (ET.n (ET.e 97 22699 199) (ET.n (ET.e 181 22807 197) (ET.e 5743 22973 194)))) (ET.n (ET.n (ET.e 17 23053 193) (ET.n (ET.e 19 23143 191) (ET.e 37 23311 187))) (ET.n (ET.e 37 23459 185) (ET.n (ET.e 3931 23587 182) (ET.e 61 23669 181))))) (ET.n (ET.n (ET.n (ET.e 2969 23753 179) (ET.n (ET.e 17 23869 177) (ET.e 37 23977 176))) (ET.n (ET.e 12041 24083 174) (ET.n (ET.e 31 24181 172) (ET.e 17 24379 168)))) (ET.n (ET.n (ET.e 17 24481 166) (ET.n (ET.e 947 24623 164) (ET.e 4127 24763 162))) (ET.n (ET.n (ET.e 17 24889 160) (ET.e 6247 24989 158)) (ET.n (ET.e 17 25127 156) (ET.e 41 25339 152))))))))
private def etCase3_5 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 7 71 137380) (ET.n (ET.e 17 137 71136) (ET.e 19 229 42501))) (ET.n (ET.e 11 331 29355) (ET.n (ET.e 97 389 24958) (ET.e 19 457 21225)))) (ET.n (ET.n (ET.e 19 571 16951) (ET.n (ET.e 17 647 14944) (ET.e 59 709 13616))) (ET.n (ET.e 101 809 11915) (ET.n (ET.e 7 883 10898) (ET.e 97 971 9896))))) (ET.n (ET.n (ET.n (ET.e 181 1087 8823) (ET.n (ET.e 7 1163 8231) (ET.e 17 1259 7591))) (ET.n (ET.e 233 1399 6810) (ET.n (ET.e 31 1489 6388) (ET.e 19 1597 5945)))) (ET.n (ET.n (ET.e 61 1709 5544) (ET.n (ET.e 61 1831 5159) (ET.e 487 1949 4836))) (ET.n (ET.e 19 2053 4579) (ET.n (ET.e 269 2153 4358) (ET.e 13 2341 3994)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 151 2417 3863) (ET.n (ET.e 13 2549 3649) (ET.e 41 2707 3426))) (ET.n (ET.e 233 2797 3310) (ET.n (ET.e 1451 2903 3179) (ET.e 193 3089 2976)))) (ET.n (ET.n (ET.e 269 3229 2839) (ET.n (ET.e 151 3323 2751) (ET.e 173 3461 2633))) (ET.n (ET.e 17 3571 2547) (ET.n (ET.e 13 3719 2438) (ET.e 17 3877 2328))))) (ET.n (ET.n (ET.n (ET.e 41 4019 2239) (ET.n (ET.e 17 4217 2125) (ET.e 241 4339 2057))) (ET.n (ET.e 251 4519 1967) (ET.n (ET.e 31 4651 1906) (ET.e 13 4759 1858)))) (ET.n (ET.n (ET.e 59 4957 1773) (ET.n (ET.e 31 5023 1748) (ET.e 47 5171 1692))) (ET.n (ET.n (ET.e 263 5261 1660) (ET.e 17 5407 1610)) (ET.n (ET.e 2753 5507 1577) (ET.e 947 5683 1519))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 1453 5813 1479) (ET.n (ET.e 47 5923 1448) (ET.e 19 6043 1416))) (ET.n (ET.e 41 6151 1386) (ET.n (ET.e 1567 6269 1356) (ET.e 59 6373 1330)))) (ET.n (ET.n (ET.e 13 6553 1288) (ET.n (ET.e 17 6733 1247) (ET.e 47 6863 1220))) (ET.n (ET.e 17 6971 1197) (ET.n (ET.e 13 7177 1156) (ET.e 3623 7247 1142))))) (ET.n (ET.n (ET.n (ET.e 929 7433 1109) (ET.n (ET.e 13 7541 1089) (ET.e 19 7639 1072))) (ET.n (ET.e 277 7757 1053) (ET.n (ET.e 179 7877 1033) (ET.e 37 7993 1015)))) (ET.n (ET.n (ET.e 17 8093 999) (ET.n (ET.e 587 8219 980) (ET.e 691 8293 969))) (ET.n (ET.e 4211 8423 951) (ET.n (ET.e 13 8581 929) (ET.e 181 8689 915)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 4373 8747 907) (ET.n (ET.e 13 8893 889) (ET.e 17 9011 874))) (ET.n (ET.e 109 9157 856) (ET.n (ET.e 13 9257 845) (ET.e 181 9413 826)))) (ET.n (ET.n (ET.e 317 9511 816) (ET.n (ET.e 41 9677 798) (ET.e 163 9781 786))) (ET.n (ET.e 4943 9887 776) (ET.n (ET.e 719 10067 758) (ET.e 509 10181 746))))) (ET.n (ET.n (ET.n (ET.e 1033 10331 732) (ET.n (ET.e 181 10499 717) (ET.e 2677 10709 698))) (ET.n (ET.e 2713 10853 686) (ET.n (ET.e 5501 11003 674) (ET.e 47 11093 666)))) (ET.n (ET.n (ET.e 563 11261 652) (ET.n (ET.e 271 11383 643) (ET.e 479 11497 634))) (ET.n (ET.n (ET.e 31 11719 617) (ET.e 1487 11897 605)) (ET.n (ET.e 461 11987 599) (ET.e 1013 12157 586)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 41 12301 577) (ET.n (ET.e 47 12409 570) (ET.e 17 12547 561))) (ET.n (ET.e 61 12689 552) (ET.n (ET.e 641 12821 544) (ET.e 19 12959 536)))) (ET.n (ET.n (ET.e 37 13099 528) (ET.n (ET.e 2203 13219 520) (ET.e 269 13451 507))) (ET.n (ET.e 151 13591 500) (ET.n (ET.e 107 13697 494) (ET.e 3457 13829 486))))) (ET.n (ET.n (ET.n (ET.e 17 13907 482) (ET.n (ET.e 167 14029 476) (ET.e 19 14251 465))) (ET.n (ET.e 41 14351 461) (ET.n (ET.e 17 14519 452) (ET.e 37 14653 446)))) (ET.n (ET.n (ET.e 107 14767 440) (ET.n (ET.e 829 14923 434) (ET.e 167 15031 428))) (ET.n (ET.e 2531 15187 421) (ET.n (ET.e 37 15319 416) (ET.e 19 15391 413)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 15581 405) (ET.n (ET.e 2621 15727 398) (ET.e 241 15907 391))) (ET.n (ET.e 73 16061 385) (ET.n (ET.e 269 16141 382) (ET.e 61 16349 374)))) (ET.n (ET.n (ET.e 2753 16519 367) (ET.n (ET.e 17 16661 362) (ET.e 37 16799 357))) (ET.n (ET.e 2111 16889 354) (ET.n (ET.e 947 17047 349) (ET.e 17 17239 342))))) (ET.n (ET.n (ET.n (ET.e 263 17359 338) (ET.n (ET.e 37 17539 332) (ET.e 227 17707 327))) (ET.n (ET.e 17 17783 324) (ET.n (ET.e 41 17959 318) (ET.e 17 18089 314)))) (ET.n (ET.n (ET.e 17 18191 311) (ET.n (ET.e 41 18287 308) (ET.e 769 18457 303))) (ET.n (ET.n (ET.e 17 18769 294) (ET.e 9461 18923 289)) (ET.n (ET.e 1367 19139 283) (ET.e 401 19249 281))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 19381 277) (ET.n (ET.e 541 19477 275) (ET.e 19 19609 270))) (ET.n (ET.e 37 19759 266) (ET.n (ET.e 41 19927 262) (ET.e 10061 20123 258)))) (ET.n (ET.n (ET.e 17 20231 255) (ET.n (ET.e 1699 20389 250) (ET.e 19 20521 247))) (ET.n (ET.e 17 20707 243) (ET.n (ET.e 1297 20753 242) (ET.e 59 20887 239))))) (ET.n (ET.n (ET.n (ET.e 269 20983 237) (ET.n (ET.e 41 21157 233) (ET.e 37 21313 228))) (ET.n (ET.e 31 21391 227) (ET.n (ET.e 19 21509 224) (ET.e 109 21583 223)))) (ET.n (ET.n (ET.e 37 21683 221) (ET.n (ET.e 10883 21767 219) (ET.e 19 21851 217))) (ET.n (ET.e 19 22003 214) (ET.n (ET.e 19 22079 213) (ET.e 5557 22229 209)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 11171 22343 206) (ET.n (ET.e 2251 22511 203) (ET.e 263 22619 201))) (ET.n (ET.e 811 22709 199) (ET.n (ET.e 31 22817 197) (ET.e 1277 22987 194)))) (ET.n (ET.n (ET.e 61 23059 193) (ET.n (ET.e 11579 23159 191) (ET.e 107 23327 187))) (ET.n (ET.e 163 23473 184) (ET.n (ET.e 983 23593 182) (ET.e 263 23671 181))))) (ET.n (ET.n (ET.n (ET.e 17 23767 179) (ET.n (ET.e 181 23893 177) (ET.e 109 23981 175))) (ET.n (ET.e 73 24091 174) (ET.n (ET.e 263 24197 171) (ET.e 271 24391 168)))) (ET.n (ET.n (ET.e 12251 24503 166) (ET.n (ET.e 12329 24659 163) (ET.e 61 24767 162))) (ET.n (ET.n (ET.e 17 24923 159) (ET.e 37 25013 158)) (ET.n (ET.e 839 25171 155) (ET.e 6337 25349 152))))))))
private def etCase3_6 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 13 79 123460) (ET.n (ET.e 37 149 65399) (ET.e 7 239 40717))) (ET.n (ET.e 7 337 28830) (ET.n (ET.e 11 397 24453) (ET.e 7 463 20948)))) (ET.n (ET.n (ET.e 37 593 16317) (ET.n (ET.e 163 653 14805) (ET.e 11 727 13276))) (ET.n (ET.e 41 821 11738) (ET.n (ET.e 151 907 10605) (ET.e 61 977 9834))))) (ET.n (ET.n (ET.n (ET.e 109 1091 8790) (ET.n (ET.e 13 1171 8173) (ET.e 641 1283 7446))) (ET.n (ET.e 31 1427 6673) (ET.n (ET.e 107 1499 6345) (ET.e 73 1607 5907)))) (ET.n (ET.n (ET.e 41 1723 5493) (ET.n (ET.e 13 1847 5113) (ET.e 13 1951 4831))) (ET.n (ET.e 1031 2063 4555) (ET.n (ET.e 37 2221 4219) (ET.e 17 2347 3983)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 173 2423 3853) (ET.n (ET.e 17 2551 3646) (ET.e 271 2711 3421))) (ET.n (ET.e 1409 2819 3283) (ET.n (ET.e 19 2927 3151) (ET.e 37 3109 2956)))) (ET.n (ET.n (ET.e 13 3251 2819) (ET.n (ET.e 13 3329 2745) (ET.e 577 3463 2632))) (ET.n (ET.e 179 3581 2539) (ET.n (ET.e 47 3761 2406) (ET.e 97 3881 2325))))) (ET.n (ET.n (ET.n (ET.e 61 4027 2234) (ET.n (ET.e 19 4219 2124) (ET.e 19 4409 2021))) (ET.n (ET.e 17 4523 1965) (ET.n (ET.e 97 4657 1903) (ET.e 797 4783 1848)))) (ET.n (ET.n (ET.e 13 4967 1769) (ET.n (ET.e 101 5051 1737) (ET.e 1297 5189 1685))) (ET.n (ET.n (ET.e 13 5279 1653) (ET.e 41 5413 1608)) (ET.n (ET.e 31 5519 1573) (ET.e 1423 5693 1516))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 97 5821 1477) (ET.n (ET.e 2963 5927 1447) (ET.e 3023 6047 1415))) (ET.n (ET.e 13 6163 1383) (ET.n (ET.e 19 6271 1356) (ET.e 13 6397 1324)))) (ET.n (ET.n (ET.e 17 6563 1286) (ET.n (ET.e 13 6761 1241) (ET.e 17 6869 1218))) (ET.n (ET.e 109 6977 1195) (ET.n (ET.e 3593 7187 1155) (ET.e 37 7253 1141))))) (ET.n (ET.n (ET.n (ET.e 233 7457 1104) (ET.n (ET.e 17 7549 1087) (ET.e 3821 7643 1071))) (ET.n (ET.e 431 7759 1052) (ET.n (ET.e 13 7879 1032) (ET.e 13 8009 1012)))) (ET.n (ET.n (ET.e 811 8111 997) (ET.n (ET.e 823 8231 978) (ET.e 17 8297 969))) (ET.n (ET.e 41 8447 948) (ET.n (ET.e 269 8609 925) (ET.e 41 8693 914)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 73 8761 906) (ET.n (ET.e 1487 8923 885) (ET.e 751 9013 873))) (ET.n (ET.e 2293 9173 854) (ET.n (ET.e 17 9283 842) (ET.e 17 9419 826)))) (ET.n (ET.n (ET.e 17 9521 815) (ET.n (ET.e 173 9689 797) (ET.e 233 9787 786))) (ET.n (ET.e 41 9923 772) (ET.n (ET.e 839 10069 758) (ET.e 19 10223 742))))) (ET.n (ET.n (ET.n (ET.e 41 10333 732) (ET.n (ET.e 73 10513 716) (ET.e 17 10711 698))) (ET.n (ET.e 61 10859 685) (ET.n (ET.e 19 11021 672) (ET.e 17 11119 663)))) (ET.n (ET.n (ET.e 1409 11273 651) (ET.n (ET.e 41 11399 642) (ET.e 17 11527 632))) (ET.n (ET.n (ET.e 17 11731 616) (ET.e 541 11903 604)) (ET.n (ET.e 1201 12011 597) (ET.e 19 12161 586)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 61 12323 576) (ET.n (ET.e 107 12413 570) (ET.e 523 12553 561))) (ET.n (ET.e 73 12703 551) (ET.n (ET.e 2137 12823 544) (ET.e 2161 12967 535)))) (ET.n (ET.n (ET.e 6551 13103 527) (ET.n (ET.e 947 13259 518) (ET.e 37 13469 506))) (ET.n (ET.e 41 13613 498) (ET.n (ET.e 2287 13723 493) (ET.e 461 13831 486))))) (ET.n (ET.n (ET.n (ET.e 37 13913 482) (ET.n (ET.e 251 14057 475) (ET.e 59 14279 464))) (ET.n (ET.e 109 14389 458) (ET.n (ET.e 173 14533 451) (ET.e 349 14659 445)))) (ET.n (ET.n (ET.e 19 14783 440) (ET.n (ET.e 3733 14933 433) (ET.e 251 15061 427))) (ET.n (ET.e 17 15199 421) (ET.n (ET.e 479 15329 415) (ET.e 31 15439 411)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 17 15607 404) (ET.n (ET.e 19 15733 398) (ET.e 17 15913 391))) (ET.n (ET.e 2677 16063 385) (ET.n (ET.e 577 16157 382) (ET.e 101 16363 374)))) (ET.n (ET.n (ET.e 1033 16529 367) (ET.n (ET.e 107 16693 361) (ET.e 41 16811 357))) (ET.n (ET.e 47 16921 353) (ET.n (ET.e 19 17063 348) (ET.e 719 17257 341))))) (ET.n (ET.n (ET.n (ET.e 181 17377 337) (ET.n (ET.e 61 17569 331) (ET.e 41 17713 327))) (ET.n (ET.e 59 17819 323) (ET.n (ET.e 107 17977 317) (ET.e 9059 18119 313)))) (ET.n (ET.n (ET.e 19 18203 311) (ET.n (ET.e 61 18301 308) (ET.e 31 18539 301))) (ET.n (ET.n (ET.e 19 18773 293) (ET.e 9479 18959 288)) (ET.n (ET.e 19 19153 283) (ET.e 9629 19259 280))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 277 19391 277) (ET.n (ET.e 17 19483 274) (ET.e 983 19661 269))) (ET.n (ET.e 41 19763 266) (ET.n (ET.e 499 19961 261) (ET.e 17 20129 257)))) (ET.n (ET.n (ET.e 2531 20249 254) (ET.n (ET.e 31 20399 250) (ET.e 59 20533 247))) (ET.n (ET.e 19 20711 243) (ET.n (ET.e 97 20759 242) (ET.e 1493 20903 238))))) (ET.n (ET.n (ET.n (ET.e 17 21013 236) (ET.n (ET.e 107 21187 232) (ET.e 73 21317 228))) (ET.n (ET.e 1783 21397 227) (ET.n (ET.e 163 21517 224) (ET.e 251 21587 223)))) (ET.n (ET.n (ET.e 241 21691 220) (ET.n (ET.e 5443 21773 219) (ET.e 3643 21859 217))) (ET.n (ET.e 5503 22013 214) (ET.n (ET.e 47 22091 212) (ET.e 227 22247 208)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 37 22349 206) (ET.n (ET.e 751 22531 203) (ET.e 11321 22643 201))) (ET.n (ET.e 1033 22727 199) (ET.n (ET.e 2287 22871 196) (ET.e 479 22993 194)))) (ET.n (ET.n (ET.e 887 23063 193) (ET.n (ET.e 17 23189 189) (ET.e 19 23333 187))) (ET.n (ET.e 181 23531 183) (ET.n (ET.e 19 23599 182) (ET.e 47 23689 181))))) (ET.n (ET.n (ET.n (ET.e 19 23789 179) (ET.n (ET.e 569 23899 177) (ET.e 2999 23993 175))) (ET.n (ET.e 251 24097 174) (ET.n (ET.e 12101 24203 171) (ET.e 12203 24407 167)))) (ET.n (ET.n (ET.e 19 24511 166) (ET.n (ET.e 2467 24671 163) (ET.e 59 24781 161))) (ET.n (ET.n (ET.e 277 24931 159) (ET.e 139 25021 158)) (ET.n (ET.e 17 25229 154) (ET.e 2113 25357 151))))))))
private def etCase3_7 : ET := ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 41 83 117506) (ET.n (ET.e 13 157 62061) (ET.e 7 281 34614))) (ET.n (ET.e 173 347 27995) (ET.n (ET.e 17 409 23732) (ET.e 233 467 20768)))) (ET.n (ET.n (ET.e 13 599 16152) (ET.n (ET.e 7 659 14669) (ET.e 61 733 13166))) (ET.n (ET.e 7 827 11652) (ET.n (ET.e 7 911 10558) (ET.e 7 1009 9517))))) (ET.n (ET.n (ET.n (ET.e 7 1093 8774) (ET.n (ET.e 59 1181 8103) (ET.e 7 1289 7410))) (ET.n (ET.e 17 1429 6663) (ET.n (ET.e 151 1511 6293) (ET.e 13 1613 5884)))) (ET.n (ET.n (ET.e 433 1733 5460) (ET.n (ET.e 31 1861 5073) (ET.e 17 1973 4775))) (ET.n (ET.e 47 2069 4542) (ET.n (ET.e 13 2237 4187) (ET.e 47 2351 3976)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 61 2441 3819) (ET.n (ET.e 37 2591 3587) (ET.e 151 2719 3410))) (ET.n (ET.e 59 2833 3266) (ET.n (ET.e 13 2939 3137) (ET.e 13 3121 2944)))) (ET.n (ET.n (ET.e 271 3253 2817) (ET.n (ET.e 37 3331 2744) (ET.e 17 3469 2627))) (ET.n (ET.e 601 3607 2519) (ET.n (ET.e 269 3767 2401) (ET.e 31 3907 2309))))) (ET.n (ET.n (ET.n (ET.e 13 4057 2216) (ET.n (ET.e 151 4229 2118) (ET.e 13 4421 2015))) (ET.n (ET.e 2273 4547 1954) (ET.n (ET.e 37 4663 1901) (ET.e 19 4789 1846)))) (ET.n (ET.n (ET.e 277 4987 1762) (ET.n (ET.e 47 5077 1727) (ET.e 433 5197 1683))) (ET.n (ET.n (ET.e 241 5303 1645) (ET.e 181 5431 1602)) (ET.n (ET.e 31 5581 1550) (ET.e 19 5701 1513))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 139 5839 1472) (ET.n (ET.e 2969 5939 1444) (ET.e 17 6053 1412))) (ET.n (ET.e 1549 6197 1374) (ET.n (ET.e 523 6277 1354) (ET.e 107 6421 1319)))) (ET.n (ET.n (ET.e 73 6571 1284) (ET.n (ET.e 3389 6779 1237) (ET.e 31 6883 1215))) (ET.n (ET.e 233 6991 1193) (ET.n (ET.e 31 7193 1153) (ET.e 19 7297 1133))))) (ET.n (ET.n (ET.n (ET.e 17 7481 1100) (ET.n (ET.e 3779 7559 1086) (ET.e 61 7687 1064))) (ET.n (ET.e 59 7789 1048) (ET.n (ET.e 563 7883 1032) (ET.e 167 8017 1011)))) (ET.n (ET.n (ET.e 31 8123 995) (ET.n (ET.e 13 8243 977) (ET.e 277 8311 967))) (ET.n (ET.e 47 8461 946) (ET.n (ET.e 479 8623 923) (ET.e 4349 8699 913)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 8779 903) (ET.n (ET.e 31 8929 885) (ET.e 37 9029 871))) (ET.n (ET.e 17 9181 854) (ET.n (ET.e 101 9293 841) (ET.e 41 9431 824)))) (ET.n (ET.n (ET.e 2383 9533 813) (ET.n (ET.e 101 9697 796) (ET.e 109 9811 783))) (ET.n (ET.e 17 9929 771) (ET.n (ET.e 5039 10079 757) (ET.e 569 10243 740))))) (ET.n (ET.n (ET.n (ET.e 17 10337 732) (ET.n (ET.e 47 10529 714) (ET.e 2683 10733 696))) (ET.n (ET.e 181 10861 685) (ET.n (ET.e 37 11027 672) (ET.e 929 11149 661)))) (ET.n (ET.n (ET.e 5639 11279 651) (ET.n (ET.e 163 11411 641) (ET.e 31 11657 622))) (ET.n (ET.n (ET.e 19 11743 616) (ET.e 1987 11923 603)) (ET.n (ET.e 17 12037 595) (ET.e 3049 12197 584)))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 17 12343 574) (ET.n (ET.e 37 12433 569) (ET.e 1571 12569 560))) (ET.n (ET.e 227 12713 550) (ET.n (ET.e 1069 12829 543) (ET.e 47 12973 535)))) (ET.n (ET.n (ET.e 41 13121 526) (ET.n (ET.e 277 13297 516) (ET.e 3373 13493 505))) (ET.n (ET.e 619 13619 498) (ET.n (ET.e 19 13757 491) (ET.e 173 13841 486))))) (ET.n (ET.n (ET.n (ET.e 179 13963 479) (ET.n (ET.e 7043 14087 473) (ET.e 17 14281 464))) (ET.n (ET.e 7211 14423 456) (ET.n (ET.e 97 14551 450) (ET.e 19 14669 445)))) (ET.n (ET.n (ET.e 2467 14803 439) (ET.n (ET.e 97 14939 433) (ET.e 3769 15077 426))) (ET.n (ET.e 317 15217 420) (ET.n (ET.e 73 15331 415) (ET.e 19 15467 410)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 19 15619 403) (ET.n (ET.e 61 15739 398) (ET.e 19 15923 390))) (ET.n (ET.e 277 16067 385) (ET.n (ET.e 31 16183 381) (ET.e 31 16369 374)))) (ET.n (ET.n (ET.e 251 16567 366) (ET.n (ET.e 1193 16703 361) (ET.e 601 16829 356))) (ET.n (ET.e 31 16927 353) (ET.n (ET.e 1423 17077 348) (ET.e 19 17291 340))))) (ET.n (ET.n (ET.n (ET.e 109 17441 335) (ET.n (ET.e 17 17579 331) (ET.e 277 17729 326))) (ET.n (ET.e 2971 17827 323) (ET.n (ET.e 31 17981 317) (ET.e 151 18121 313)))) (ET.n (ET.n (ET.e 569 18209 310) (ET.n (ET.e 109 18313 307) (ET.e 19 18583 300))) (ET.n (ET.n (ET.e 31 18787 293) (ET.e 17 18973 288)) (ET.n (ET.e 17 19177 282) (ET.e 19 19267 280))))))) (ET.n (ET.n (ET.n (ET.n (ET.n (ET.e 109 19403 277) (ET.n (ET.e 31 19531 272) (ET.e 41 19681 268))) (ET.n (ET.e 1237 19793 266) (ET.n (ET.e 17 19993 261) (ET.e 73 20149 257)))) (ET.n (ET.n (ET.e 1013 20261 254) (ET.n (ET.e 19 20407 250) (ET.e 10271 20543 247))) (ET.n (ET.e 5179 20717 243) (ET.n (ET.e 31 20771 241) (ET.e 523 20921 238))))) (ET.n (ET.n (ET.n (ET.e 37 21017 236) (ET.n (ET.e 163 21191 232) (ET.e 17 21319 228))) (ET.n (ET.e 107 21401 227) (ET.n (ET.e 269 21521 224) (ET.e 257 21589 223)))) (ET.n (ET.n (ET.e 31 21701 220) (ET.n (ET.e 3631 21787 218) (ET.e 17 21863 217))) (ET.n (ET.e 3671 22027 214) (ET.n (ET.e 263 22093 212) (ET.e 31 22259 208)))))) (ET.n (ET.n (ET.n (ET.n (ET.e 233 22369 206) (ET.n (ET.e 17 22543 202) (ET.e 151 22651 200))) (ET.n (ET.e 11369 22739 199) (ET.n (ET.e 19 22877 196) (ET.e 31 23003 194)))) (ET.n (ET.n (ET.e 769 23071 193) (ET.n (ET.e 1933 23197 189) (ET.e 19 23371 186))) (ET.n (ET.e 1471 23537 183) (ET.n (ET.e 227 23609 182) (ET.e 2371 23711 180))))) (ET.n (ET.n (ET.n (ET.e 17 23801 179) (ET.n (ET.e 139 23909 177) (ET.e 4001 24007 175))) (ET.n (ET.e 17 24107 173) (ET.n (ET.e 97 24251 170) (ET.e 17 24413 167)))) (ET.n (ET.n (ET.e 227 24517 166) (ET.n (ET.e 31 24677 163) (ET.e 1033 24793 161))) (ET.n (ET.n (ET.e 4157 24943 159) (ET.e 569 25037 157)) (ET.n (ET.e 601 25243 154) (ET.e 1153 25367 151))))))))
private def etCase3 : ET :=
  ET.n (ET.n (ET.n etCase3_0 etCase3_1) (ET.n etCase3_2 etCase3_3)) (ET.n (ET.n etCase3_4 etCase3_5) (ET.n etCase3_6 etCase3_7))

private lemma etCase1_valid : etCase1.valid = true := by rfl
private lemma etCase2_valid : etCase2.valid = true := by rfl
private lemma etCase3_valid : etCase3.valid = true := by rfl

private lemma case1_bound :
    Nat.ble (Nat.add (weightOf 3) (Nat.add etCase1.sumC (sumTrie (stepCase filt1) 8 0 etCase1.toTrie))) BUDGET = true := by
  rfl

private lemma case2_bound :
    Nat.ble (Nat.add (weightOf 5) (Nat.add etCase2.sumC (sumTrie (stepCase filt2) 8 0 etCase2.toTrie))) BUDGET = true := by
  rfl

private lemma case3_bound :
    Nat.ble (Nat.add etCase3.sumC (sumTrie (stepCase filt3) 8 0 etCase3.toTrie)) BUDGET = true := by
  rfl

private theorem digits_ge_13000 (a : ℕ) (ha : AgohGiuga.IsStrongGiuga a) :
    13000 ≤ (Nat.digits 10 a).length := by
  obtain ⟨_, _, hodd, hnorm, _⟩ := strongGiuga_props ha
  apply digits_ge_13000_of_weight_bound ha
  set S := a.primeFactors
  set Slt := S.filter (· < 40000)
  by_cases h3 : 3 ∈ S
  · have h3lt : 3 ∈ Slt := Finset.mem_filter.mpr ⟨h3, by norm_num⟩
    have hsplit : ∑ p ∈ Slt, weightOf p = weightOf 3 + ∑ p ∈ Slt.erase 3, weightOf p :=
      (Finset.add_sum_erase _ _ h3lt).symm
    rw [hsplit]
    have hfilt1 : ∀ p ∈ Slt.erase 3, filt1 p = true := by
      intro p hp
      have hp_ne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
      have hp_S : p ∈ S := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_S
      have hndvd3 : ¬ (3 ∣ p) := fun h => hp_ne3 (((hp_prime.eq_one_or_self_of_dvd 3 h).resolve_left (by omega)).symm)
      have hndvd_pm1 : ¬ (3 ∣ p - 1) := hnorm 3 h3 p hp_S
      have hmod2 : p % 3 = 2 := by
        have h3p : 3 ≤ p := (hodd p hp_S).2
        have h0 : p % 3 ≠ 0 := fun h => hndvd3 (Nat.dvd_of_mod_eq_zero h)
        have h1 : p % 3 ≠ 1 := fun h => hndvd_pm1 (Nat.dvd_of_mod_eq_zero (by omega))
        omega
      exact Nat.beq_eq.mpr hmod2
    have hle := sum_weight_filter_le (Slt.erase 3) filt1 etCase1
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
      (fun p hp => hodd p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
      (fun p hp q hq => hnorm p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
                                q (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).1)
      (fun p hp => (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2)
      hfilt1 etCase1_valid
    have hbnd := Nat.ble_eq.mp case1_bound
    rw [nat_add, nat_add] at hbnd
    omega
  · by_cases h5 : 5 ∈ S
    · have h5lt : 5 ∈ Slt := Finset.mem_filter.mpr ⟨h5, by norm_num⟩
      have hsplit : ∑ p ∈ Slt, weightOf p = weightOf 5 + ∑ p ∈ Slt.erase 5, weightOf p :=
        (Finset.add_sum_erase _ _ h5lt).symm
      rw [hsplit]
      have hfilt2 : ∀ p ∈ Slt.erase 5, filt2 p = true := by
        intro p hp
        have hp_ne5 : p ≠ 5 := (Finset.mem_erase.mp hp).1
        have hp_S : p ∈ S := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
        have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ hp_S)
        have hndvd_pm1 : ¬ (5 ∣ p - 1) := hnorm 5 h5 p hp_S
        have h3p : 3 ≤ p := (hodd p hp_S).2
        have hmod1 : p % 5 ≠ 1 := fun h => hndvd_pm1 (Nat.dvd_of_mod_eq_zero (by omega))
        unfold filt2
        have hb3 : Nat.beq p 3 = false := by
          cases h : Nat.beq p 3 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne3
        have hb5 : Nat.beq p 5 = false := by
          cases h : Nat.beq p 5 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne5
        have hbm : Nat.beq (Nat.mod p 5) 1 = false := by
          cases h : Nat.beq (Nat.mod p 5) 1 with
          | false => rfl
          | true => exact absurd (Nat.beq_eq.mp h) hmod1
        rw [hb3, hb5, hbm]
      have hle := sum_weight_filter_le (Slt.erase 5) filt2 etCase2
        (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
        (fun p hp => hodd p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
        (fun p hp q hq => hnorm p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
                                  q (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).1)
        (fun p hp => (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2)
        hfilt2 etCase2_valid
      have hbnd := Nat.ble_eq.mp case2_bound
      rw [nat_add, nat_add] at hbnd
      omega
    · have hfilt3 : ∀ p ∈ Slt, filt3 p = true := by
        intro p hp
        have hp_S : p ∈ S := (Finset.mem_filter.mp hp).1
        have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ hp_S)
        have hp_ne5 : p ≠ 5 := fun h => h5 (h ▸ hp_S)
        unfold filt3
        have hb3 : Nat.beq p 3 = false := by
          cases h : Nat.beq p 3 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne3
        have hb5 : Nat.beq p 5 = false := by
          cases h : Nat.beq p 5 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne5
        rw [hb3, hb5]
      have hle := sum_weight_filter_le Slt filt3 etCase3
        (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        (fun p hp => hodd p (Finset.mem_filter.mp hp).1)
        (fun p hp q hq => hnorm p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1)
        (fun p hp => (Finset.mem_filter.mp hp).2)
        hfilt3 etCase3_valid
      have hbnd := Nat.ble_eq.mp case3_bound
      rw [nat_add] at hbnd
      omega

end AgohGiugaSolution

theorem OMA.solution : type_of% @AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga := by
  intro a ha
  have h := AgohGiugaSolution.digits_ge_13000 a ha
  omega
