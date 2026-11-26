import FormalConjectures.ErdosProblems.«978»

/-! A finite sieve modulo the product of the small prime powers supplies residue
classes. Counting their translates in complete periods gives a lower bound in a
dyadic interval. The large-prime estimate counts all inputs lost above the cutoff.

For the analytic background, see T. D. Browning,
[*Power-free values of polynomials*](https://doi.org/10.1007/s00013-011-0224-7) (2011). -/

namespace OMA.R_Erdos978_erdos_978_variants_sub_two_R1

open scoped Classical

/-- A positive fraction of each period survives all primes up to the cutoff.
The denominator bound is chosen before the cutoff. -/
def H1 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ)) →
    ∃ C : ℕ, 0 < C ∧ ∀ Y : ℕ,
      let primes := (Finset.range (Y + 1)).filter Nat.Prime
      let Q := ∏ p ∈ primes, p ^ k
      Q ≤ C * ((Finset.range Q).filter fun (r : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ Y → ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card

/-- For every reciprocal accuracy, fix a cutoff after which the excluded inputs
have less than that fraction of every sufficiently large dyadic interval. -/
def H2 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ Y N₀ : ℕ, ∀ N ≥ N₀,
      A * ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ Y < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < N

/-- Lift the surviving residues through a whole number of periods. -/
lemma count_complete_periods (P : ℕ → Prop) (Q m : ℕ) (hQ : 0 < Q)
    (hshift : ∀ i r : ℕ, P r → P (i * Q + r)) :
    m * ((Finset.range Q).filter P).card ≤
      ((Finset.Ico (m * Q) (2 * (m * Q))).filter P).card := by
  classical
  let R := (Finset.range Q).filter P
  let grid := (Finset.range m) ×ˢ R
  let G := (Finset.Ico (m * Q) (2 * (m * Q))).filter P
  let index : ℕ × ℕ → ℕ := fun z => (m + z.1) * Q + z.2
  have residue_lt {r : ℕ} (hr : r ∈ R) : r < Q :=
    Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hc : grid.card ≤ G.card := by
    apply Finset.card_le_card_of_injOn index
    · rintro ⟨i, r⟩ h
      obtain ⟨hi, hr⟩ := Finset.mem_product.mp h
      have him := Finset.mem_range.mp hi
      have hl : m * Q ≤ (m + i) * Q + r := by
        rw [Nat.add_mul]
        omega
      have hh : (m + i) * Q + r < 2 * (m * Q) := calc
        _ < (m + i) * Q + Q := Nat.add_lt_add_left (residue_lt hr) _
        _ = (m + i + 1) * Q := by ring
        _ ≤ (m + m) * Q := Nat.mul_le_mul_right Q (by omega)
        _ = _ := by ring
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hl, hh⟩,
        hshift (m + i) r (Finset.mem_filter.mp hr).2⟩
    · rintro ⟨i, r⟩ hx ⟨j, s⟩ hy he
      change (m + i) * Q + r = (m + j) * Q + s at he
      have hr := residue_lt (Finset.mem_product.mp hx).2
      have hs := residue_lt (Finset.mem_product.mp hy).2
      have hrs : r = s := by
        simpa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using congrArg (fun x => x % Q) he
      subst s
      have hij := Nat.eq_of_mul_eq_mul_right hQ (Nat.add_right_cancel he)
      exact Prod.ext (by omega) rfl
  simpa [grid, R, G] using hc

lemma avoid_prime_on_shift (f : Polynomial ℤ) (k p Q i r : ℕ) (hdiv : p ^ k ∣ Q)
    (hr : ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)) :
    ¬ (p : ℤ) ^ k ∣ f.eval ((i * Q + r : ℕ) : ℤ) := by
  intro hd
  have hz : i * Q ≡ 0 [MOD p ^ k] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hdiv i)
  have he : i * Q + r ≡ r [MOD p ^ k] := by simpa only [zero_add] using hz.add_right r
  have hdiff : (p : ℤ) ^ k ∣ (r : ℤ) - ((i * Q + r : ℕ) : ℤ) := by
    simpa only [Nat.cast_pow] using he.dvd
  have hval := hdiff.trans (Polynomial.sub_dvd_eval_sub (r : ℤ) ((i * Q + r : ℕ) : ℤ) f)
  exact hr (by simpa only [sub_add_cancel] using dvd_add hval hd)

lemma powerfree_of_avoid_primes {a : ℤ} {k : ℕ}
    (h : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ k ∣ a) : Powerfree k a := by
  intro x hx
  by_contra hu
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (mt Int.isUnit_iff_natAbs_eq.mpr hu)
  exact h p hp ((pow_dvd_pow_of_dvd (Int.natCast_dvd.mpr hpx) k).trans hx)

/-- It suffices to beat the explicit finite-sieve count at one fixed cutoff on
arbitrarily late complete blocks. The tail counts every hit in the block, including
hits among residues that the finite sieve already excludes. -/
lemma infinite_of_tail_below_period_count (f : Polynomial ℤ) (k Y Q : ℕ) (hQ : 0 < Q)
    (hperiod : ∀ p : ℕ, p.Prime → p ≤ Y → p ^ k ∣ Q)
    (htail :
      let R := (Finset.range Q).filter fun (r : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ Y → ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)
      ∀ L : ℕ, ∃ m : ℕ, L < m * Q ∧
        ((Finset.Ico (m * Q) (2 * (m * Q))).filter fun (n : ℕ) =>
          ∃ p : ℕ, p.Prime ∧ Y < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < m * R.card) :
    {n : ℕ | Powerfree k (f.eval (n : ℤ))}.Infinite := by
  classical
  let survives (n : ℕ) := ∀ p : ℕ, p.Prime → p ≤ Y → ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have shift (i r : ℕ) (hr : survives r) : survives (i * Q + r) := by
    intro p hp hpY
    exact avoid_prime_on_shift f k p Q i r (hperiod p hp hpY) (hr p hp hpY)
  apply Set.infinite_of_forall_exists_gt
  intro L
  obtain ⟨m, hL, hloss⟩ := htail L
  let N := m * Q
  let G := (Finset.Ico N (2 * N)).filter survives
  let B := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ Y < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have hgap : B.card < G.card :=
    hloss.trans_le (count_complete_periods survives Q m hQ shift)
  obtain ⟨n, hnG, hnB⟩ := Finset.exists_mem_notMem_of_card_lt_card hgap
  obtain ⟨hnI, hnsmall⟩ := Finset.mem_filter.mp hnG
  refine ⟨n, powerfree_of_avoid_primes ?_, hL.trans_le (Finset.mem_Ico.mp hnI).1⟩
  intro p hp hdiv
  by_cases hpY : p ≤ Y
  · exact hnsmall p hp hpY hdiv
  · exact hnB (Finset.mem_filter.mpr ⟨hnI, p, hp, Nat.lt_of_not_ge hpY, hdiv⟩)

theorem main : H1 → H2 → type_of% @Erdos978.erdos_978.variants.sub_two := by
  classical
  intro hlocal htail f hirr hdeg hadm
  obtain ⟨C, hC, hcount⟩ := hlocal f hirr hdeg hadm
  obtain ⟨Y, N₀, hlarge⟩ := htail f hirr hdeg C hC
  let k := f.natDegree - 2
  let S := (Finset.range (Y + 1)).filter Nat.Prime
  let Q := ∏ p ∈ S, p ^ k
  let R := (Finset.range Q).filter fun (r : ℕ) =>
    ∀ p : ℕ, p.Prime → p ≤ Y → ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)
  have hQ : 0 < Q := Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos k)
  have hR : Q ≤ C * R.card := hcount Y
  apply infinite_of_tail_below_period_count f k Y Q hQ
  · intro p hp hpY
    have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    exact Finset.dvd_prod_of_mem _ hpS
  · dsimp only
    intro L
    let m := max (L + 1) N₀
    let N := m * Q
    have hmN : m ≤ N := Nat.le_mul_of_pos_right m hQ
    have hN₀ : N₀ ≤ N := (le_max_right (L + 1) N₀).trans hmN
    refine ⟨m, lt_of_lt_of_le (Nat.lt_succ_self L) ((le_max_left (L + 1) N₀).trans hmN), ?_⟩
    let B := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
      ∃ p : ℕ, p.Prime ∧ Y < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
    change B.card < m * R.card
    have hB : C * B.card < N := hlarge N hN₀
    have hbound : N ≤ C * (m * R.card) := calc
      _ ≤ m * (C * R.card) := Nat.mul_le_mul_left m hR
      _ = _ := by ring
    by_contra! h
    exact (hB.trans_le hbound).not_ge (Nat.mul_le_mul_left C h)

end OMA.R_Erdos978_erdos_978_variants_sub_two_R1
