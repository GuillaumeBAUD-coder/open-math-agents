import OMAReductions.R_Erdos978_erdos_978_variants_sub_two_R1

/-! Local admissibility gives a positive Euler factor at every prime.
The root count at all sufficiently large primes makes the excluded proportions
summable, and the Chinese remainder theorem gives the uniform finite-sieve bound. -/

namespace Erdos978LocalSieve

open scoped Classical

lemma finite_products_bounded_below {ι : Type*} (w : ι → ℝ) (hw : Summable w)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∀ i, w i < 1) :
    ∃ C : ℕ, 0 < C ∧ ∀ S : Finset ι, (1 : ℝ) / C ≤ ∏ i ∈ S, (1 - w i) := by
  classical
  have hpos (i : ι) : 0 < 1 - w i := sub_pos.mpr (h1 i)
  have hlog : Summable (fun i => Real.log (1 - w i)) := by
    simpa [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hw.neg
  let c := Real.exp (∑' i, Real.log (1 - w i))
  have hprod : HasProd (fun i => 1 - w i) c := Real.hasProd_of_hasSum_log hpos hlog.hasSum
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (Real.exp_pos (∑' i, Real.log (1 - w i)))
  refine ⟨m + 1, Nat.succ_pos _, ?_⟩
  intro S
  have hlower : c ≤ ∏ i ∈ S, (1 - w i) := by
    apply le_of_tendsto hprod
    filter_upwards [Filter.eventually_ge_atTop S] with T hT
    exact Finset.prod_le_prod_of_subset_of_le_one hT (fun i _ => (hpos i).le)
      (fun i _ _ => sub_le_self _ (h0 i))
  have hm' : (1 : ℝ) / (m + 1 : ℕ) ≤ c := by simpa [c] using hm.le
  exact hm'.trans hlower

lemma prime_products_bounded_below (k : ℕ) (hk : 1 < k) (roots : ℕ → ℕ)
    (hproper : ∀ p : ℕ, p.Prime → roots p < p ^ k)
    (hbound : ∃ D Y₀ : ℕ, ∀ p : ℕ, p.Prime → Y₀ < p → roots p ≤ D) :
    ∃ C : ℕ, 0 < C ∧ ∀ Y : ℕ, (1 : ℝ) / C ≤
      ∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, (1 - (roots p : ℝ) / (p : ℝ) ^ k) := by
  classical
  obtain ⟨D, Y₀, hD⟩ := hbound
  let w (p : ℕ) : ℝ := if p.Prime then (roots p : ℝ) / (p : ℝ) ^ k else 0
  have wn (p : ℕ) : 0 ≤ w p := by dsimp [w]; split <;> positivity
  have wo (p : ℕ) : w p < 1 := by
    by_cases hp : p.Prime
    · have hden : 0 < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.pos) _
      simp only [w, if_pos hp, div_lt_one hden]
      exact_mod_cast hproper p hp
    · simp [w, hp]
  have hs : Summable (fun p : ℕ => (D : ℝ) * (1 / (p : ℝ) ^ k)) :=
    (Real.summable_one_div_nat_pow.mpr hk).mul_left (D : ℝ)
  have hw : Summable w := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop Y₀] with p hpY
    rw [Real.norm_eq_abs, abs_of_nonneg (wn p)]
    by_cases hp : p.Prime
    · simp only [w, if_pos hp, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hD p hp hpY) (by positivity)
    · simp only [w, if_neg hp]
      positivity
  obtain ⟨C, hC, hc⟩ := finite_products_bounded_below w hw wn wo
  refine ⟨C, hC, fun Y => (hc ((Finset.range (Y + 1)).filter Nat.Prime)).trans_eq ?_⟩
  apply Finset.prod_congr rfl
  intro p hp
  simp [w, (Finset.mem_filter.mp hp).2]

lemma root_count_lt_modulus (f : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (h : ∃ n : ℕ, ¬ (q : ℤ) ∣ f.eval (n : ℤ)) :
    ((Finset.range q).filter fun (r : ℕ) => (q : ℤ) ∣ f.eval (r : ℤ)).card < q := by
  obtain ⟨n, hn⟩ := h
  have ha : ¬ (q : ℤ) ∣ f.eval ((n % q : ℕ) : ℤ) := by
    intro bad
    have hd := (Nat.mod_modEq n q).dvd.trans (Polynomial.sub_dvd_eval_sub
      (n : ℤ) ((n % q : ℕ) : ℤ) f)
    exact hn (by simpa only [sub_add_cancel] using dvd_add hd bad)
  have hproper :
      ((Finset.range q).filter fun (r : ℕ) => (q : ℤ) ∣ f.eval (r : ℤ)) ⊂ Finset.range q := by
    apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    exact ⟨n % q, Finset.mem_range.mpr (Nat.mod_lt n hq), fun hh => ha (Finset.mem_filter.mp hh).2⟩
  simpa only [Finset.card_range] using Finset.card_lt_card hproper

/-- Distinct choices of a surviving residue at each prime give distinct
surviving residues in a full period. -/
lemma crt_surviving_count (f : Polynomial ℤ) (k : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, ((Finset.range (p ^ k)).filter fun (r : ℕ) =>
      ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card) ≤
    ((Finset.range (∏ p ∈ S, p ^ k)).filter fun (n : ℕ) =>
      ∀ p ∈ S, ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card := by
  classical
  let G (p : ℕ) := (Finset.range (p ^ k)).filter fun (r : ℕ) => ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)
  let Q := ∏ p ∈ S, p ^ k
  let target := (Finset.range Q).filter fun (n : ℕ) => ∀ p ∈ S, ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let vals (a : ∀ i : S, G i) (p : ℕ) : ℕ := if h : p ∈ S then (a ⟨p, h⟩).val else 0
  have hnz (p : ℕ) (hp : p ∈ S) : p ^ k ≠ 0 := pow_ne_zero _ (hS p hp).ne_zero
  have hco : (↑S : Set ℕ).Pairwise (fun p q : ℕ => (p ^ k).Coprime (q ^ k)) :=
    fun p hp q hq hpq => Nat.coprime_pow_primes _ _ (hS p hp) (hS q hq) hpq
  let crt (a : ∀ i : S, G i) := Nat.chineseRemainderOfFinset (vals a) (fun p : ℕ => p ^ k) S hnz hco
  have hmod (a : ∀ i : S, G i) (i : S) :
      (crt a).val ≡ (a i).val [MOD i.val ^ k] := by
    simpa [vals, i.property] using (crt a).property i.val i.property
  have hmem (a : ∀ i : S, G i) : (crt a).val ∈ target := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.chineseRemainderOfFinset_lt_prod (vals a) _ hnz hco), ?_⟩
    intro p hp bad
    let i : S := ⟨p, hp⟩
    have hd : (p : ℤ) ^ k ∣ ((a i).val : ℤ) - ((crt a).val : ℤ) := by
      simpa only [Nat.cast_pow] using (hmod a i).dvd
    have hval := hd.trans (Polynomial.sub_dvd_eval_sub ((a i).val : ℤ) ((crt a).val : ℤ) f)
    exact (Finset.mem_filter.mp (a i).property).2 (by simpa only [sub_add_cancel] using dvd_add hval bad)
  let pack (a : ∀ i : S, G i) : target := ⟨(crt a).val, hmem a⟩
  have hinj : Function.Injective pack := by
    intro a b h
    have hval : (crt a).val = (crt b).val := congrArg Subtype.val h
    funext i
    apply Subtype.ext
    have hab := (hmod a i).symm.trans (hval ▸ hmod b i)
    exact hab.eq_of_lt_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp (a i).property).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp (b i).property).1)
  have hc := Fintype.card_le_of_injective pack hinj
  change (∏ p ∈ S, (G p).card) ≤ target.card
  rw [← Finset.prod_coe_sort (s := S) (f := fun p : ℕ => (G p).card)]
  simpa only [Fintype.card_pi, Fintype.card_coe] using hc

lemma local_density_from_root_bound (f : Polynomial ℤ) (k : ℕ) (hk : 1 < k)
    (hadm : ∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ))
    (hbound : ∃ D Y₀ : ℕ, ∀ p : ℕ, p.Prime → Y₀ < p →
      ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card ≤ D) :
    ∃ C : ℕ, 0 < C ∧ ∀ Y : ℕ,
      let S := (Finset.range (Y + 1)).filter Nat.Prime
      let Q := ∏ p ∈ S, p ^ k
      Q ≤ C * ((Finset.range Q).filter fun (r : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ Y → ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card := by
  classical
  let bad (p : ℕ) := ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card
  let good (p : ℕ) := ((Finset.range (p ^ k)).filter fun (r : ℕ) => ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card
  have proper (p : ℕ) (hp : p.Prime) : bad p < p ^ k := by
    simpa only [bad, Nat.cast_pow] using root_count_lt_modulus f (p ^ k) (pow_pos hp.pos _)
      (by simpa only [Nat.cast_pow] using hadm p hp)
  obtain ⟨C, hC, hc⟩ := prime_products_bounded_below k hk bad proper hbound
  refine ⟨C, hC, ?_⟩
  intro Y
  let S := (Finset.range (Y + 1)).filter Nat.Prime
  let Q := ∏ p ∈ S, p ^ k
  have prime {p : ℕ} (hp : p ∈ S) : p.Prime := (Finset.mem_filter.mp hp).2
  have hQ : 0 < Q := Finset.prod_pos (fun p hp => pow_pos (prime hp).pos _)
  have ratio (p : ℕ) (hp : p ∈ S) :
      1 - (bad p : ℝ) / (p : ℝ) ^ k = (good p : ℝ) / (p : ℝ) ^ k := by
    have hcq : bad p + good p = p ^ k := by
      simpa only [bad, good, Finset.card_range] using (Finset.range (p ^ k)).card_filter_add_card_filter_not
        (fun r : ℕ => (p : ℤ) ^ k ∣ f.eval (r : ℤ))
    have hcqr : (bad p : ℝ) + (good p : ℝ) = (p : ℝ) ^ k := by exact_mod_cast hcq
    have hd : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (prime hp).ne_zero)
    field_simp
    linarith
  have heq : (∏ p ∈ S, (1 - (bad p : ℝ) / (p : ℝ) ^ k)) =
      ((∏ p ∈ S, good p : ℕ) : ℝ) / (Q : ℝ) := by
    calc
      _ = ∏ p ∈ S, ((good p : ℝ) / (p : ℝ) ^ k) := Finset.prod_congr rfl ratio
      _ = _ := by simp only [Q, Nat.cast_prod, Nat.cast_pow, Finset.prod_div_distrib]
  have hr := (hc Y).trans_eq heq
  have hnum : (Q : ℝ) ≤ (C : ℝ) * ((∏ p ∈ S, good p : ℕ) : ℝ) := by
    have := (div_le_div_iff₀ (by exact_mod_cast hC) (by exact_mod_cast hQ)).mp hr
    simpa only [one_mul, mul_comm] using this
  have hn : Q ≤ C * ∏ p ∈ S, good p := by exact_mod_cast hnum
  apply hn.trans
  apply Nat.mul_le_mul_left
  apply (crt_surviving_count f k S (fun p hp => prime hp)).trans
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnQ, hnS⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnQ, ?_⟩
  intro p hp hpY
  exact hnS p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

end Erdos978LocalSieve

namespace Erdos978RootCount

open Polynomial

/-- Gauss's lemma and separability over the rationals give a nonzero integral resultant. -/
lemma derivative_resultant_ne_zero (f : ℤ[X]) (hi : Irreducible f) (hd : f.natDegree ≠ 0) :
    f.resultant f.derivative ≠ 0 := by
  let φ := Int.castRingHom ℚ
  have hφ : Function.Injective φ := Int.cast_injective
  have hirr : Irreducible (f.map φ) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hi.isPrimitive hd)).mp hi
  have hcop : IsCoprime (f.map φ) (f.derivative.map φ) := by
    simpa only [derivative_map] using (separable_def _).mp hirr.separable
  have hr := resultant_ne_zero (f.map φ) (f.derivative.map φ) hcop
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map] at hr
  exact fun h => hr (by rw [h, map_zero])

/-- Evaluating the resultant identity excludes a common root with the derivative. -/
lemma not_dvd_derivative_at_root (f : ℤ[X]) (hd : f.natDegree ≠ 0) (p x : ℤ)
    (hres : ¬ p ∣ f.resultant f.derivative) (hx : p ∣ f.eval x) :
    ¬ p ∣ f.derivative.eval x := by
  obtain ⟨a, b, _, _, hbez⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
    le_rfl le_rfl (Or.inl hd)
  have he := congrArg (fun g : ℤ[X] => g.eval x) hbez
  simp only [eval_add, eval_mul, eval_C] at he
  intro hdx
  apply hres
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_left hdx _)

/-- Two roots above the same simple residue agree modulo the whole prime power. -/
lemma simple_lifts_congruent (f : ℤ[X]) {p k : ℕ} (hp : p.Prime) {x y : ℤ}
    (hx : (p : ℤ) ^ k ∣ f.eval x) (hy : (p : ℤ) ^ k ∣ f.eval y)
    (hxy : (p : ℤ) ∣ y - x) (hs : ¬ (p : ℤ) ∣ f.derivative.eval x) :
    (p : ℤ) ^ k ∣ y - x := by
  obtain ⟨c, ht⟩ := exists_mul_sq_add_linear_part_eq_eval_add f x (y - x)
  rw [show x + (y - x) = y by ring] at ht
  have hfactor : (f.derivative.eval x + c * (y - x)) * (y - x) = f.eval y - f.eval x := by
    linear_combination ht
  have hunit : ¬ (p : ℤ) ∣ f.derivative.eval x + c * (y - x) := by
    intro h
    have hcd := dvd_mul_of_dvd_right hxy c
    exact hs (by simpa only [add_sub_cancel_right] using dvd_sub h hcd)
  apply (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left k hunit
  rw [hfactor]
  exact dvd_sub hy hx

lemma count_lifts_le_degree (f : ℤ[X]) (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0)
    (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff)
    (hs : ∀ x : ℤ, (p : ℤ) ∣ f.eval x → ¬ (p : ℤ) ∣ f.derivative.eval x) :
    ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card ≤
      f.natDegree := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let φ := Int.castRingHom (ZMod p)
  let g := f.map φ
  have hgne : g ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff f.natDegree) hz
    have he : (f.leadingCoeff : ZMod p) = 0 := by simpa [g, φ, coeff_map] using hc
    exact hlc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he)
  let S := (Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)
  have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ k := dvd_pow_self _ hk
  have hcard : S.card ≤ g.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ZMod p))
    · intro n hn
      have hb : (p : ℤ) ∣ f.eval (n : ℤ) := hpdiv.trans (Finset.mem_filter.mp hn).2
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hgne).mpr
      change (f.map φ).eval (n : ZMod p) = 0
      have hcast : φ (n : ℤ) = (n : ZMod p) := by simp [φ]
      rw [← hcast, eval_map_apply]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
    · intro n hn m hm he
      obtain ⟨hnr, hfn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hmr, hfm⟩ := Finset.mem_filter.mp hm
      have hmod := (ZMod.natCast_eq_natCast_iff n m p).mp he
      have hpow := simple_lifts_congruent f hp hfn hfm hmod.dvd (hs n (hpdiv.trans hfn))
      have hlift : n ≡ m [MOD p ^ k] :=
        Nat.modEq_of_dvd (by simpa only [Nat.cast_pow] using hpow)
      exact hlift.eq_of_lt_of_lt (Finset.mem_range.mp hnr) (Finset.mem_range.mp hmr)
  exact hcard.trans ((Multiset.toFinset_card_le g.roots).trans
    (card_roots_map_le_natDegree (f := φ) f))

end Erdos978RootCount

open Erdos978RootCount Polynomial in
lemma Erdos978RootCount.eventual_bound (f : ℤ[X]) (hi : Irreducible f) (hd : 9 ≤ f.natDegree) :
    ∃ D Y₀ : ℕ, 0 < D ∧ ∀ p : ℕ, p.Prime → Y₀ < p →
      ((Finset.range (p ^ (f.natDegree - 2))).filter fun (r : ℕ) =>
        (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (r : ℤ)).card ≤ D := by
  let R := f.resultant f.derivative
  refine ⟨f.natDegree, max f.leadingCoeff.natAbs R.natAbs, by omega, ?_⟩
  intro p hp hlarge
  have avoid (z : ℤ) (hz : z ≠ 0) (hlt : z.natAbs < p) : ¬ (p : ℤ) ∣ z := by
    intro h
    exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natCast_dvd.mp h))
  apply count_lifts_le_degree f p (f.natDegree - 2) hp (by omega)
  · exact avoid _ (leadingCoeff_ne_zero.mpr hi.ne_zero) ((le_max_left _ _).trans_lt hlarge)
  · intro x hx
    have hR := avoid R (derivative_resultant_ne_zero f hi (by omega))
      ((le_max_right _ _).trans_lt hlarge)
    exact not_dvd_derivative_at_root f (by omega) p x hR hx

theorem OMA.solution : OMA.R_Erdos978_erdos_978_variants_sub_two_R1.H1 := by
  intro f hi hd
  dsimp only
  intro hadm
  obtain ⟨D, Y₀, _, hD⟩ := Erdos978RootCount.eventual_bound f hi hd
  exact Erdos978LocalSieve.local_density_from_root_bound f (f.natDegree - 2) (by omega) hadm ⟨D, Y₀, hD⟩
