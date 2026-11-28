import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3

/-!
# Bounding runs of high jumps among simple prime factors

Let E consist of the simple support primes q for which 32 divides q+1 and
the odd part d(q) of q+1 is another support prime. In a balanced completion
the downward map d is injective on E. For internal edges whose exponent
v₂(q+1) is divisible by five, the nonzero residues modulo 31 increase by
one. This bounds the number of high vertices by 30 times the combined
number of exits and internal jumps with exponent outside that class.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H2_R2


/-- An injective map from the good vertices raises a bounded integer weight
by one. The total weight outside the good vertices bounds their number. -/
theorem count_by_weight {α : Type*} [DecidableEq α] (E G : Finset α)
    (f : α → α) (w : α → ℕ) (L : ℕ) (sub : G ⊆ E)
    (image : ∀ x ∈ G, f x ∈ E) (inj : Set.InjOn f (G : Set α))
    (rise : ∀ x ∈ G, w (f x) = w x + 1) (cap : ∀ x ∈ E, w x ≤ L) :
    E.card ≤ (L + 1) * (E \ G).card := by
  have subset : G.image f ⊆ E := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact image x hx
  have imageSum : ∑ x ∈ G, w (f x) ≤ ∑ x ∈ E, w x := by
    rw [← Finset.sum_image (f := w) (show ∀ x ∈ G, ∀ y ∈ G, f x = f y → x = y from
      fun _ hx _ hy h => inj hx hy h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_congr rfl rise, Finset.sum_add_distrib, Finset.sum_const,
    Nat.nsmul_eq_mul, Nat.mul_one] at imageSum
  have split := Finset.sum_sdiff sub (f := w)
  have unused : (∑ x ∈ E \ G, w x) ≤ (E \ G).card * L := by
    calc
      _ ≤ ∑ _x ∈ E \ G, L := Finset.sum_le_sum
        (fun x hx => cap x (Finset.mem_sdiff.mp hx).1)
      _ = _ := by simp
  have count := Finset.card_sdiff_add_card_eq_card sub
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm L]
  omega

/-- At all admissible high vertices the residue modulo 31 is nonzero. -/
theorem high_nonzero_mod {S : Finset ℕ} (valid : ∀ p ∈ S, p.Prime ∧ 3 ≤ p)
    {q : ℕ} (qs : q ∈ S) (ds : ordCompl[2] (1+q) ∈ S) : q % 31 ≠ 0 := by
  intro zero
  have eq : q = 31 := ((valid q qs).1.dvd_iff_eq (by decide : 31 ≠ 1)).mp
    (Nat.dvd_iff_mod_eq_zero.mpr zero)
  subst q
  have by31 : ordCompl[2] (1+31) = 1 := by
    change 32 / 2 ^ (32 : ℕ).factorization 2 = 1
    have fac : (32 : ℕ).factorization 2 = 5 := by
      rw [show (32 : ℕ) = 2^5 by decide, Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
    rw [fac]
    decide
  rw [by31] at ds
  have := (valid 1 ds).2
  omega

theorem residue_budget (S : Finset ℕ) (valid : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    let d := fun q : ℕ => ordCompl[2] (1+q)
    let E := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1+q)
    Set.InjOn d (E : Set ℕ) →
    E.card ≤ 30 * (E.filter (fun q => d q ∉ E ∨ d q % 31 ≠ (1+q) % 31)).card := by
  intro d E inj
  let G := E.filter (fun q => d q ∈ E ∧ d q % 31 = (1+q) % 31)
  let w := fun q : ℕ => q % 31 - 1
  have good : G ⊆ E := Finset.filter_subset ..
  have nonzero (q : ℕ) (hq : q ∈ E) : q % 31 ≠ 0 := by
    obtain ⟨qs, ds, _⟩ := Finset.mem_filter.mp hq
    exact high_nonzero_mod valid qs ds
  have rise (q : ℕ) (hq : q ∈ G) : w (d q) = w q + 1 := by
    obtain ⟨qe, de, he⟩ := Finset.mem_filter.mp hq
    have hq' := nonzero q qe
    have hd' := nonzero (d q) de
    dsimp [w]
    omega
  have total := count_by_weight E G d w 29 good
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) (fun _ hx _ hy => inj (good hx) (good hy))
    rise (fun q _ => by dsimp [w]; omega)
  have eq : E \ G = E.filter (fun q => d q ∉ E ∨ d q % 31 ≠ (1+q) % 31) := by
    ext q
    simp only [G, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [eq] at total
  exact total

/-- A power of 32 is one modulo 31. Thus an aligned shift increases the
downward residue by one even when successive shift exponents differ. -/
theorem aligned_shift (q : ℕ) (aligned : 5 ∣ (1+q).factorization 2) :
    ordCompl[2] (1+q) % 31 = (1+q) % 31 := by
  obtain ⟨k, hk⟩ := aligned
  have base : (2 : ℕ)^5 ≡ 1 [MOD 31] := by decide
  have power : (2 : ℕ)^(1+q).factorization 2 ≡ 1 [MOD 31] := by
    rw [hk, pow_mul]
    simpa only [one_pow] using base.pow k
  have step := power.mul_right (ordCompl[2] (1+q))
  simpa only [Nat.ModEq, Nat.ordProj_mul_ordCompl_eq_self, one_mul] using step.symm

/-- Taking odd parts in the completion identity accounts for all demands at
once. The remaining odd product divides the fixed core times the support. -/
theorem balanced_injective {c a : ℕ} {S : Finset ℕ} (hc : Odd c)
    (support : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2^a*c)
    (balance : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)) *
        (∏ q ∈ S, (1+q)) = (2*(2^a*c)) * (∏ q ∈ S, q)) :
    let d := fun q : ℕ => ordCompl[2] (1+q)
    let E := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1+q)
    Set.InjOn d (E : Set ℕ) := by
  intro d E
  let oddPart : ℕ →* ℕ := {
    toFun := fun n => ordCompl[2] n
    map_one' := by simp [Nat.factorization_one]
    map_mul' := fun x y => Nat.ordCompl_mul x y 2 }
  have divide : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q := by
    have hprod : (∏ q ∈ S, d q) = oddPart (∏ q ∈ S, (1+q)) :=
      (map_prod oddPart (fun q : ℕ => 1+q) S).symm
    rw [hprod]
    calc
      _ ∣ oddPart ((∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)) *
          (∏ q ∈ S, (1+q))) := by rw [map_mul]; exact dvd_mul_left _ _
      _ = oddPart (2^(a+1) * (c * ∏ q ∈ S, q)) := by
        rw [balance, pow_succ]
        congr 1
        ac_rfl
      _ = ordCompl[2] (c * ∏ q ∈ S, q) := Nat.ordCompl_self_pow_mul _ _ Nat.prime_two
      _ ∣ _ := Nat.ordCompl_dvd _ _
  intro q hq r hr equal
  obtain ⟨qs, dq, _⟩ := Finset.mem_filter.mp (show q ∈ E from hq)
  have rs := (Finset.mem_filter.mp (show r ∈ E from hr)).1
  exact OMA.R_Erdos1052_erdos_1052_R2_H2_R3.demand_inj hc.pos.ne' (fun p hp => (support p hp).1)
    (fun p hp hpc => (support p hp).2 (dvd_mul_of_dvd_right hpc _))
    (fun p _ => (Nat.ordCompl_pos 2 (by omega : 1+p ≠ 0)).ne') divide qs rs dq equal

/-- Bound the number of high vertices whose demand leaves the high set. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      let d := fun q : ℕ => ordCompl[2] (1+q)
      let E := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1+q)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      (E.filter (fun q => d q ∉ E)).card ≤ K

/-- Bound the internal high jumps whose exponents are not multiples of five. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      let d := fun q : ℕ => ordCompl[2] (1+q)
      let E := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1+q)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      (E.filter (fun q => d q ∈ E ∧ ¬ 5 ∣ (1+q).factorization 2)).card ≤ K

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3.H2 := by
  intro exits exceptional c hc powerful
  obtain ⟨A, hA⟩ := exits c hc powerful
  obtain ⟨B, hB⟩ := exceptional c hc powerful
  refine ⟨30 * (A + B), ?_⟩
  intro a S b u ha hsize interval support balance
  let d := fun q : ℕ => ordCompl[2] (1+q)
  let E := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1+q)
  let ends := E.filter (fun q => d q ∉ E)
  let jumps := E.filter (fun q => d q ∈ E ∧ ¬ 5 ∣ (1+q).factorization 2)
  have hends : ends.card ≤ A := hA a S ha hsize interval support balance
  have hjumps : jumps.card ≤ B := hB a S ha hsize interval support balance
  have valid (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 3 ≤ p :=
    ⟨(support p hp).1, (Finset.mem_Icc.mp (interval hp)).1⟩
  have graph := residue_budget S valid (balanced_injective hc support balance)
  have cover : E.filter (fun q => d q ∉ E ∨ d q % 31 ≠ (1+q) % 31) ⊆ ends ∪ jumps := by
    intro q hq
    obtain ⟨qe, bad⟩ := Finset.mem_filter.mp hq
    by_cases inside : d q ∈ E
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨qe, inside,
        fun ha => (bad.resolve_left (not_not_intro inside)) (aligned_shift q ha)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨qe, inside⟩)
  calc
    E.card ≤ _ := graph
    _ ≤ 30 * (ends ∪ jumps).card := Nat.mul_le_mul_left 30 (Finset.card_le_card cover)
    _ ≤ 30 * (ends.card + jumps.card) := Nat.mul_le_mul_left 30 (Finset.card_union_le ends jumps)
    _ ≤ _ := Nat.mul_le_mul_left 30 (Nat.add_le_add hends hjumps)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H2_R2
