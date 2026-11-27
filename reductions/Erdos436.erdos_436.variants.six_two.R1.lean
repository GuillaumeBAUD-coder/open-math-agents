import FormalConjectures.ErdosProblems.«436»

-- Reduction Erdos436.erdos_436.variants.six_two.R1 of Erdős Problem 436 — six two
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `Λ(6, 2) = 202124`

* `H1` is a finite search: every labelling `w` of the primes by `ZMod 6` has some `n ≤ 202124` such
  that the `w`-weighted prime factor sums of `n` and of `n + 1` both vanish.  Applied to `w = ` the
  discrete logarithm modulo `6` with respect to a primitive root of `ZMod p`, it gives two
  consecutive sixth powers `n, n + 1 ≤ 202125` modulo every prime `p > 202125`, hence the upper bound.
  (This lifting follows the approach of the merged reduction
  `Erdos436.erdos_436.variants.three_two.R1`.)
* `H2` is the lower bound of Lehmer, Lehmer and Mills: for infinitely many primes `p` the first
  pair of consecutive sixth power residues starts at `202124` or later.
-/

namespace OMA.R_Erdos436_erdos_436_variants_six_two_R1

open Filter Erdos436

/-- Every labelling of the primes modulo `6` has two successive zero sums below `202125`. -/
def H1 : Prop :=
  ∀ w : ℕ → ZMod 6, ∃ n ∈ Finset.Icc 1 202124,
    (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0

/-- Lehmer–Lehmer–Mills: arbitrarily large primes have no consecutive sixth power residues
below `202124`. -/
def H2 : Prop :=
  ∀ B : ℕ, ∃ p > B, p.Prime ∧ 202124 ≤ r 6 2 p

lemma lift_sum {p : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (e : ℕ → ℤ)
    (l : List ℕ) (h : ∀ q ∈ l, ((g ^ e q : (ZMod p)ˣ) : ZMod p) = q) :
    ((g ^ (l.map e).sum : (ZMod p)ˣ) : ZMod p) = l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, zpow_add, Units.val_mul,
      Nat.cast_mul]
    rw [h q (by simp), ih (fun a ha => h a (by simp [ha]))]

lemma upper (search : H1) {p : ℕ} (hp : p.Prime) (hbig : 202125 < p) :
    r 6 2 p ≤ 202124 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let unit (q : ℕ) : (ZMod p)ˣ := if h : (q : ZMod p) ≠ 0 then Units.mk0 _ h else 1
  have hexp (q : ℕ) : ∃ t : ℤ, g ^ t = unit q := hg (unit q)
  choose e he using hexp
  have nz {n : ℕ} (hn : 0 < n) (hs : n ≤ 202125) : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun d => (Nat.not_le.mpr (hs.trans_lt hbig)) (Nat.le_of_dvd hn d)
  have sixth {n : ℕ} (hn : 0 < n) (hs : n ≤ 202125)
      (hc : (n.primeFactorsList.map (fun q => (e q : ZMod 6))).sum = 0) :
      IsPowerResidue 6 p n := by
    have hc' : (((n.primeFactorsList.map e).sum : ℤ) : ZMod 6) = 0 := by
      simpa [List.map_map, Function.comp_def] using hc
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mp hc'
    have h := lift_sum g e n.primeFactorsList (fun q hq => by
      rw [he]
      simp [unit, nz (Nat.pos_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs)])
    rw [Nat.prod_primeFactorsList hn.ne', ha, mul_comm, zpow_mul] at h
    exact ⟨nz hn hs, ((g ^ a : (ZMod p)ˣ) : ZMod p), by simpa using h⟩
  obtain ⟨n, hi, hn, hn'⟩ := search (fun q => (e q : ZMod 6))
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hi
  have hr : 1 ≤ n ∧ ∀ i < 2, IsPowerResidue 6 p (n + i) := by
    refine ⟨hl, ?_⟩
    intro i hi
    interval_cases i
    · simpa using sixth (by omega) (by omega) hn
    · exact sixth (by omega) (by omega) hn'
  exact (iInf₂_le n hr).trans (by exact_mod_cast hu)

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.variants.six_two := by
  intro search primes
  rw [runLimsup, Filter.limsup_eq]
  apply le_antisymm
  · apply sInf_le
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_gt_atTop (202125 : ℕ)] with p hp hprime
    exact upper search hprime hp
  · apply le_sInf
    intro b hb
    have h : ∀ᶠ p in atTop, p.Prime → r 6 2 p ≤ b := eventually_inf_principal.mp hb
    obtain ⟨B, hB⟩ := eventually_atTop.mp h
    obtain ⟨p, hpB, hp, hr⟩ := primes B
    exact hr.trans (hB p hpB.le hp)

end OMA.R_Erdos436_erdos_436_variants_six_two_R1
