import FormalConjectures.ErdosProblems.«436»

/-! Separate the finite search over quartic characters from the realization of one
extremal character pattern by arbitrarily large primes. H1 only needs the values
at the primes up to 1225. H2 prescribes Euler's quartic character on rational primes.
The proof checks the entire lower obstruction through 1223 and lifts the upper
search to a primitive root of the finite field. -/

namespace OMA.R_Erdos436_erdos_436_variants_four_two_R1
open Filter Erdos436

/-- Every labeling of the small primes modulo four has two successive zero sums. -/
def H1 : Prop :=
  ∀ w : ℕ → ZMod 4, ∃ n ∈ Finset.Icc 1 1224,
    (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0

/-- Realize one explicit quartic character pattern at arbitrarily large primes. -/
def H2 : Prop :=
  let weight := fun q : ℕ =>
    ((0x400000000000000000000400000000000000000000000004000004000000400404400000000004000400004400000004400004400000000000000000400000000000000000000404000400004000400000000000404000000000004000000000000000004400004400000000000000000004000000004000004000000000000000000000000000400400000004400000000400000000000000000000000000400000004400000000000000000000000000000000400000404000000000000004000000000004400004400004000404000000404004004000400404000000000000000404404000000000004000004400400400400000000404400000000000000404400000000000404004004000004400404000000408004400000800400004400004400400404404008400004404404410 : ℕ) >>> (2*q)) % 4
  ∀ B : ℕ, ∃ p > B, p.Prime ∧ 4 ∣ p - 1 ∧
    ∃ u : ZMod p, IsPrimitiveRoot u 4 ∧ ∀ q : ℕ, q.Prime → q ≤ 1224 →
      (q : ZMod p)^((p-1)/4) = u^(weight q : ℕ)

lemma lift_sum {p : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (e : ℕ → ℤ)
    (l : List ℕ) (h : ∀ q ∈ l, ((g ^ e q : (ZMod p)ˣ) : ZMod p) = q) :
    ((g ^ (l.map e).sum : (ZMod p)ˣ) : ZMod p) = l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons,List.sum_cons,List.prod_cons,zpow_add,Units.val_mul,Nat.cast_mul]
    rw [h q (by simp),ih (fun a ha => h a (by simp [ha]))]

private lemma upper (search : H1) {p : ℕ} (hp : p.Prime) (hbig : 1225 < p) :
    r 4 2 p ≤ 1224 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let unit (q : ℕ) : (ZMod p)ˣ := if h : (q : ZMod p) ≠ 0 then Units.mk0 _ h else 1
  have hexp (q : ℕ) : ∃ t : ℤ, g ^ t = unit q := hg (unit q)
  choose e he using hexp
  have nz {n : ℕ} (hn : 0 < n) (hs : n ≤ 1225) : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun d => (Nat.not_le.mpr (hs.trans_lt hbig)) (Nat.le_of_dvd hn d)
  have quartic {n : ℕ} (hn : 0 < n) (hs : n ≤ 1225)
      (hc : (n.primeFactorsList.map (fun q => (e q : ZMod 4))).sum = 0) :
      IsPowerResidue 4 p n := by
    have hc' : (((n.primeFactorsList.map e).sum : ℤ) : ZMod 4) = 0 := by
      simpa [List.map_map, Function.comp_def] using hc
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hc'
    have h := lift_sum g e n.primeFactorsList (fun q hq => by
      rw [he]
      simp [unit,nz (Nat.pos_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs)])
    rw [Nat.prod_primeFactorsList hn.ne', ha, mul_comm, zpow_mul] at h
    exact ⟨nz hn hs, ((g ^ a : (ZMod p)ˣ) : ZMod p), by simpa using h⟩
  obtain ⟨n,hi,hn,hn'⟩ := search (fun q => (e q : ZMod 4))
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hi
  have hr : 1 ≤ n ∧ ∀ i < 2, IsPowerResidue 4 p (n+i) := by
    refine ⟨hl,?_⟩
    intro i hi
    interval_cases i
    · simpa using quartic (by omega) (by omega) hn
    · exact quartic (by omega) (by omega) hn'
  exact (iInf₂_le n hr).trans (by exact_mod_cast hu)

private lemma factor_character {p : ℕ} (u : ZMod p) (w : ℕ → ℕ) (m : ℕ)
    (l : List ℕ) (h : ∀ q ∈ l, (q : ZMod p)^m = u^(w q)) :
    (l.prod : ZMod p)^m = u^(l.map w).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.prod_cons,Nat.cast_mul,mul_pow,List.map_cons,List.sum_cons,pow_add]
    rw [h q (by simp),ih (fun a ha => h a (by simp [ha]))]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private lemma lower (primes : H2) (B : ℕ) : ∃ p > B, p.Prime ∧ 1224 ≤ r 4 2 p := by
  let w (q : ℕ) : ℕ :=
    ((0x400000000000000000000400000000000000000000000004000004000000400404400000000004000400004400000004400004400000000000000000400000000000000000000404000400004000400000000000404000000000004000000000000000004400004400000000000000000004000000004000004000000000000000000000000000400400000004400000000400000000000000000000000000400000004400000000000000000000000000000000400000404000000000000004000000000004400004400004000404000000404004004000400404000000000000000404404000000000004000004400400400400000000404400000000000000404400000000000404004004000004400404000000408004400000800400004400004400400404404008400004404404410 : ℕ) >>> (2*q)) % 4
  have obstruct : ∀ j : Fin 1223,
      ¬ (4 ∣ (((j.val+1).primeFactorsList.map w).sum) ∧
         4 ∣ (((j.val+2).primeFactorsList.map w).sum)) := by decide +kernel
  obtain ⟨p,hpB,hp,hd,u,hu,hpr⟩ := primes B
  let : Fact p.Prime := ⟨hp⟩
  have vanishes {n : ℕ} (hn : 0 < n) (hs : n ≤ 1224) (hc : IsPowerResidue 4 p n) :
      4 ∣ (n.primeFactorsList.map w).sum := by
    obtain ⟨hnz,x,hx⟩ := hc
    have hx0 : x ≠ 0 := fun he => hnz (by simpa [he] using hx.symm)
    have hf := factor_character u w ((p-1)/4) n.primeFactorsList (fun q hq =>
      hpr q (Nat.prime_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs))
    rw [Nat.prod_primeFactorsList hn.ne', ← hx, ← pow_mul, Nat.mul_div_cancel' hd,
      ZMod.pow_card_sub_one_eq_one hx0] at hf
    exact (hu.pow_eq_one_iff_dvd _).mp hf.symm
  refine ⟨p,hpB,hp,le_iInf₂ (fun n ⟨hn,hr⟩ => ?_)⟩
  suffices h : 1224 ≤ n by exact_mod_cast h
  by_contra! h
  let j : Fin 1223 := ⟨n-1,by omega⟩
  have hj : j.val+1 = n := by dsimp [j]; omega
  have hj' : j.val+2 = n+1 := by dsimp [j]; omega
  apply obstruct j
  rw [hj,hj']
  exact ⟨vanishes hn (by omega) (by simpa using hr 0 (by decide)),
    vanishes (by omega) (by omega) (hr 1 (by decide))⟩

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.variants.four_two := by
  intro search primes
  rw [runLimsup,Filter.limsup_eq]
  apply le_antisymm
  · apply sInf_le
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_gt_atTop (1225 : ℕ)] with p hp hprime
    exact upper search hprime hp
  · apply le_sInf
    intro b hb
    have h : ∀ᶠ p in atTop, p.Prime → r 4 2 p ≤ b := eventually_inf_principal.mp hb
    obtain ⟨B,hB⟩ := eventually_atTop.mp h
    obtain ⟨p,hpB,hp,hr⟩ := lower primes B
    exact hr.trans (hB p hpB.le hp)

end OMA.R_Erdos436_erdos_436_variants_four_two_R1
