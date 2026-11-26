import OMAReductions.R_Erdos978_erdos_978_variants_sub_two_R1

/-! Count the contribution from each prime by its polynomial roots modulo the
prime power. Up to the square root of the block parameter, a telescoping sum
controls the main terms and the number of moduli controls the rounding errors. -/

namespace OMA.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1

open scoped Classical

/-- Away from finitely many exceptional primes, the number of roots modulo the
prime power is bounded in terms of the polynomial. -/
def H1 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∃ D Y₀ : ℕ, 0 < D ∧ ∀ p : ℕ, p.Prime → Y₀ < p →
      ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card ≤ D

/-- Inputs hit by a prime above the square root of the block parameter have
vanishing relative count. -/
def H2 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ N.sqrt < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < N

section Counting

/-- Quotient and remainder embed each hit into a block paired with a root modulo the modulus. -/
lemma dyadic_hits_le_residue_count (f : Polynomial ℤ) (N q : ℕ) (hq : 0 < q) :
    ((Finset.Ico N (2 * N)).filter fun (n : ℕ) => (q : ℤ) ∣ f.eval (n : ℤ)).card ≤
      (2 * N / q + 1) *
        ((Finset.range q).filter fun (r : ℕ) => (q : ℤ) ∣ f.eval (r : ℤ)).card := by
  classical
  let hits := (Finset.Ico N (2 * N)).filter fun (n : ℕ) => (q : ℤ) ∣ f.eval (n : ℤ)
  let roots := (Finset.range q).filter fun (r : ℕ) => (q : ℤ) ∣ f.eval (r : ℤ)
  let boxes := Finset.range (2 * N / q + 1) ×ˢ roots
  have hcard : hits.card ≤ boxes.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n / q, n % q))
    · intro n hn
      obtain ⟨hI, hroot⟩ := Finset.mem_filter.mp hn
      have hquot : n / q ≤ 2 * N / q := Nat.div_le_div_right (Finset.mem_Ico.mp hI).2.le
      have hdiff := (Nat.mod_modEq n q).symm.dvd.trans
        (Polynomial.sub_dvd_eval_sub ((n % q : ℕ) : ℤ) (n : ℤ) f)
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hquot), ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hq),
        by simpa only [sub_add_cancel] using dvd_add hdiff hroot⟩
    · intro n hn m hm he
      have hquot : n / q = m / q := congrArg Prod.fst he
      have hrem : n % q = m % q := congrArg Prod.snd he
      calc
        n = n % q + q * (n / q) := (Nat.mod_add_div n q).symm
        _ = m % q + q * (m / q) := by rw [hquot, hrem]
        _ = m := Nat.mod_add_div m q
  simpa [boxes, roots, hits] using hcard

/-- Count the union over finitely many moduli by the sum of their root bounds. -/
lemma finite_sieve_loss_le_root_sum (f : Polynomial ℤ) (N k : ℕ) (S : Finset ℕ)
    (hpos : ∀ p ∈ S, 0 < p) :
    ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
      ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card ≤
      ∑ p ∈ S, (2 * N / p ^ k + 1) *
        ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card := by
  classical
  let hits (p : ℕ) := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  calc
    _ ≤ (S.biUnion hits).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hI, p, hp, hd⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hI, hd⟩⟩
    _ ≤ ∑ p ∈ S, (hits p).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun p hp => by
      simpa only [hits, Nat.cast_pow] using
        dyadic_hits_le_residue_count f N (p ^ k) (pow_pos (hpos p hp) k)

/-- The difference of successive integer quotients controls the square-denominator term. -/
lemma div_square_step (X t : ℕ) (ht : 0 < t) :
    X / (t + 1) ^ 2 + X / (t + 1) ≤ X / t := by
  have hstep : (X / (t + 1) ^ 2) * (t + 1) ≤ X / (t + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr
    rw [Nat.mul_assoc, ← pow_two]
    exact Nat.div_mul_le_self X _
  apply (Nat.le_div_iff_mul_le ht).mpr
  have hdiv := Nat.div_mul_le_self X (t + 1)
  nlinarith only [hstep, hdiv, Nat.zero_le (X / (t + 1) ^ 2)]

/-- An integral telescoping bound for the contribution from squares. -/
lemma sum_div_square (X Y B : ℕ) (hY : 0 < Y) :
    (∑ p ∈ Finset.Ioc Y B, X / p ^ 2) ≤ X / Y := by
  by_cases hb : Y ≤ B
  · suffices h : (∑ p ∈ Finset.Ioc Y B, X / p ^ 2) + X / B ≤ X / Y by
      exact (Nat.le_add_right _ _).trans h
    induction B, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      have hI : Finset.Ioc Y (b + 1) = insert (b + 1) (Finset.Ioc Y b) := by
        ext p
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      rw [hI, Finset.sum_insert (by simp)]
      have hstep := div_square_step X b (by omega)
      omega
  · simp [Finset.Ioc_eq_empty (by omega : ¬ Y < B)]

/-- A uniform root bound controls the band between the fixed cutoff and the square root. -/
lemma medium_prime_hits (f : Polynomial ℤ) (N k Y D : ℕ) (hk : 2 ≤ k) (hY : 0 < Y)
    (hroot : ∀ p : ℕ, p.Prime → Y < p →
      ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card ≤ D) :
    let S := (Finset.Ioc Y N.sqrt).filter Nat.Prime
    ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
      ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card ≤ (2 * N / Y + N.sqrt) * D := by
  classical
  intro S
  have hS : S ⊆ Finset.Ioc Y N.sqrt := Finset.filter_subset _ _
  have hprime {p : ℕ} (hp : p ∈ S) : p.Prime := (Finset.mem_filter.mp hp).2
  have hsum : (∑ p ∈ S, 2 * N / p ^ 2) ≤ 2 * N / Y :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)).trans
      (sum_div_square _ _ _ hY)
  have hcard : S.card ≤ N.sqrt := (Finset.card_le_card hS).trans (by simp)
  calc
    _ ≤ _ := finite_sieve_loss_le_root_sum f N k S (fun p hp => (hprime hp).pos)
    _ ≤ ∑ p ∈ S, (2 * N / p ^ 2 + 1) * D := by
      apply Finset.sum_le_sum
      intro p hp
      have hd := Nat.div_le_div_left (a := 2 * N)
        (Nat.pow_le_pow_right (hprime hp).pos hk) (pow_pos (hprime hp).pos 2)
      exact Nat.mul_le_mul (Nat.add_le_add_right hd 1)
        (hroot p (hprime hp) (Finset.mem_Ioc.mp (hS hp)).1)
    _ = ((∑ p ∈ S, 2 * N / p ^ 2) + S.card) * D := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    _ ≤ _ := Nat.mul_le_mul_right D (Nat.add_le_add hsum hcard)

end Counting

theorem main : H1 → H2 → OMA.R_Erdos978_erdos_978_variants_sub_two_R1.H2 := by
  classical
  intro hroot hfar f hi hd
  dsimp only
  intro A hA
  let k := f.natDegree - 2
  obtain ⟨D, Y₀, hD, hroots⟩ := hroot f hi hd
  obtain ⟨N₁, hlarge⟩ := hfar f hi hd (2 * A) (by omega)
  let Y := max Y₀ (8 * A * D)
  let T := 4 * A * D
  refine ⟨Y, max N₁ (T * T), ?_⟩
  intro N hN
  let S := (Finset.Ioc Y N.sqrt).filter Nat.Prime
  let middle := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let far := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ N.sqrt < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let allHits := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ Y < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have hY : 8 * A * D ≤ Y := le_max_right _ _
  have hYpos : 0 < Y := lt_of_lt_of_le (by positivity : 0 < 8 * A * D) hY
  have hm : middle.card ≤ (2 * N / Y + N.sqrt) * D :=
    medium_prime_hits f N k Y D (by dsimp [k]; omega) hYpos
      (fun p hp h => hroots p hp ((le_max_left Y₀ (8 * A * D)).trans_lt h))
  have hdiv : (8 * A * D) * (2 * N / Y) ≤ 2 * N := calc
    _ ≤ Y * (2 * N / Y) := Nat.mul_le_mul_right _ hY
    _ ≤ _ := by simpa only [Nat.mul_comm Y] using Nat.div_mul_le_self (2 * N) Y
  have hquot : (4 * A * D) * (2 * N / Y) ≤ N := by nlinarith only [hdiv]
  have hs : T ≤ N.sqrt := Nat.le_sqrt.mpr ((le_max_right N₁ (T * T)).trans hN)
  have hsqrt : (4 * A * D) * N.sqrt ≤ N :=
    (Nat.mul_le_mul_right _ hs).trans (Nat.sqrt_le N)
  have hm' : 4 * A * middle.card ≤ 2 * N := calc
    _ ≤ 4 * A * ((2 * N / Y + N.sqrt) * D) := Nat.mul_le_mul_left _ hm
    _ = (4 * A * D) * (2 * N / Y) + (4 * A * D) * N.sqrt := by ring
    _ ≤ N + N := Nat.add_le_add hquot hsqrt
    _ = _ := by ring
  have hf : 2 * A * far.card < N := hlarge N ((le_max_left N₁ (T * T)).trans hN)
  have cover : allHits ⊆ middle ∪ far := by
    intro n hn
    obtain ⟨hI, p, hp, hpY, hpn⟩ := Finset.mem_filter.mp hn
    by_cases hs : p ≤ N.sqrt
    · have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpY, hs⟩, hp⟩
      exact Finset.mem_union.mpr (.inl <| Finset.mem_filter.mpr ⟨hI, p, hpS, hpn⟩)
    · exact Finset.mem_union.mpr (.inr <|
        Finset.mem_filter.mpr ⟨hI, p, hp, Nat.lt_of_not_ge hs, hpn⟩)
  have hc := (Finset.card_le_card cover).trans (Finset.card_union_le middle far)
  have htotal := Nat.mul_le_mul_left A hc
  change A * allHits.card < N
  nlinarith only [hm', hf, htotal]

end OMA.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1
