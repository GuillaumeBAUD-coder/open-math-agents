import FormalConjectures.ErdosProblems.«436»

-- Reduction Erdos436.erdos_436.variants.five_two.R1 of Erdős Problem 436 — five two
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `Λ(5, 2) = 7888`

* `H1` is a finite search: every labelling `w` of the primes by `ZMod 5` has some `n ≤ 7888` such
  that the `w`-weighted prime factor sums of `n` and of `n + 1` both vanish.  Applied to `w = ` the
  discrete logarithm modulo `5` with respect to a primitive root of `ZMod p`, it gives two
  consecutive fifth powers `n, n + 1 ≤ 7889` modulo every prime `p > 7889`, hence the upper bound.
  (This lifting follows the approach of the merged reduction
  `Erdos436.erdos_436.variants.three_two.R1`.)
* `H2` is the lower bound of Lehmer, Lehmer and Mills: for infinitely many primes `p` the first
  pair of consecutive fifth power residues starts at `7888` or later.
-/

namespace OMA.R_Erdos436_erdos_436_variants_five_two_R1

open Filter Erdos436

/-- Every labelling of the primes modulo `5` has two successive zero sums below `7889`. -/
def H1 : Prop :=
  ∀ w : ℕ → ZMod 5, ∃ n ∈ Finset.Icc 1 7888,
    (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0

/-- Lehmer–Lehmer–Mills: arbitrarily large primes have no consecutive fifth power residues
below `7888`. -/
def H2 : Prop :=
  ∀ B : ℕ, ∃ p > B, p.Prime ∧ 7888 ≤ r 5 2 p

lemma lift_sum {p : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (e : ℕ → ℤ)
    (l : List ℕ) (h : ∀ q ∈ l, ((g ^ e q : (ZMod p)ˣ) : ZMod p) = q) :
    ((g ^ (l.map e).sum : (ZMod p)ˣ) : ZMod p) = l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, zpow_add, Units.val_mul,
      Nat.cast_mul]
    rw [h q (by simp), ih (fun a ha => h a (by simp [ha]))]

lemma upper (search : H1) {p : ℕ} (hp : p.Prime) (hbig : 7889 < p) :
    r 5 2 p ≤ 7888 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let unit (q : ℕ) : (ZMod p)ˣ := if h : (q : ZMod p) ≠ 0 then Units.mk0 _ h else 1
  have hexp (q : ℕ) : ∃ t : ℤ, g ^ t = unit q := hg (unit q)
  choose e he using hexp
  have nz {n : ℕ} (hn : 0 < n) (hs : n ≤ 7889) : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun d => (Nat.not_le.mpr (hs.trans_lt hbig)) (Nat.le_of_dvd hn d)
  have fifth {n : ℕ} (hn : 0 < n) (hs : n ≤ 7889)
      (hc : (n.primeFactorsList.map (fun q => (e q : ZMod 5))).sum = 0) :
      IsPowerResidue 5 p n := by
    have hc' : (((n.primeFactorsList.map e).sum : ℤ) : ZMod 5) = 0 := by
      simpa [List.map_map, Function.comp_def] using hc
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hc'
    have h := lift_sum g e n.primeFactorsList (fun q hq => by
      rw [he]
      simp [unit, nz (Nat.pos_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs)])
    rw [Nat.prod_primeFactorsList hn.ne', ha, mul_comm, zpow_mul] at h
    exact ⟨nz hn hs, ((g ^ a : (ZMod p)ˣ) : ZMod p), by simpa using h⟩
  obtain ⟨n, hi, hn, hn'⟩ := search (fun q => (e q : ZMod 5))
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hi
  have hr : 1 ≤ n ∧ ∀ i < 2, IsPowerResidue 5 p (n + i) := by
    refine ⟨hl, ?_⟩
    intro i hi
    interval_cases i
    · simpa using fifth (by omega) (by omega) hn
    · exact fifth (by omega) (by omega) hn'
  exact (iInf₂_le n hr).trans (by exact_mod_cast hu)

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.variants.five_two := by
  intro search primes
  rw [runLimsup, Filter.limsup_eq]
  apply le_antisymm
  · apply sInf_le
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_gt_atTop (7889 : ℕ)] with p hp hprime
    exact upper search hprime hp
  · apply le_sInf
    intro b hb
    have h : ∀ᶠ p in atTop, p.Prime → r 5 2 p ≤ b := eventually_inf_principal.mp hb
    obtain ⟨B, hB⟩ := eventually_atTop.mp h
    obtain ⟨p, hpB, hp, hr⟩ := primes B
    exact hr.trans (hB p hpB.le hp)

end OMA.R_Erdos436_erdos_436_variants_five_two_R1
