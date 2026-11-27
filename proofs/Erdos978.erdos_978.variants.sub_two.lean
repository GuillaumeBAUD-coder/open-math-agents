import FormalConjectures.ErdosProblems.«978»

section S1
namespace OMA.E978R1
open scoped Classical
def H1 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ)) →
    ∃ C : ℕ, 0 < C ∧ ∀ Y : ℕ,
      let primes := (Finset.range (Y + 1)).filter Nat.Prime
      let Q := ∏ p ∈ primes, p ^ k
      Q ≤ C * ((Finset.range Q).filter fun (r : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ Y → ¬ (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card
def H2 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ Y N₀ : ℕ, ∀ N ≥ N₀,
      A * ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ Y < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < N
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
end OMA.E978R1
end S1

section S2
namespace OMA.E978R2
open scoped Classical
def H1 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∃ D Y₀ : ℕ, 0 < D ∧ ∀ p : ℕ, p.Prime → Y₀ < p →
      ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card ≤ D
def H2 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ N.sqrt < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < N
section Counting
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
lemma div_square_step (X t : ℕ) (ht : 0 < t) :
    X / (t + 1) ^ 2 + X / (t + 1) ≤ X / t := by
  have hstep : (X / (t + 1) ^ 2) * (t + 1) ≤ X / (t + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr
    rw [Nat.mul_assoc, ← pow_two]
    exact Nat.div_mul_le_self X _
  apply (Nat.le_div_iff_mul_le ht).mpr
  have hdiv := Nat.div_mul_le_self X (t + 1)
  nlinarith only [hstep, hdiv, Nat.zero_le (X / (t + 1) ^ 2)]
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
theorem main : H1 → H2 → OMA.E978R1.H2 := by
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
end OMA.E978R2
end S2

section S3
namespace OMA.E978R3
open scoped Classical
def H1 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * (∑ p ∈ (Finset.Ioc N.sqrt N).filter Nat.Prime,
        ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card) < N
def H2 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < N
section RootCounts
lemma block_lt_prime_power {N p k : ℕ} (hp : p.Prime) (hs : N.sqrt < p) (hk : 3 ≤ k) :
    2 * N < p ^ k := by
  have hsq : N < p ^ 2 := by
    rw [pow_two]
    exact lt_of_not_ge fun h => hs.not_ge (Nat.le_sqrt.mpr h)
  calc
    2 * N < 2 * p ^ 2 := Nat.mul_lt_mul_of_pos_left hsq (by decide)
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp.two_le
    _ = p ^ 3 := by ring
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
lemma intermediate_hits_le_total_roots (f : Polynomial ℤ) (N k : ℕ) (hk : 3 ≤ k) :
    let S := (Finset.Ioc N.sqrt N).filter Nat.Prime
    ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
      ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card ≤
      ∑ p ∈ S, ((Finset.range (p ^ k)).filter fun (r : ℕ) =>
        (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card := by
  classical
  intro S
  let roots (p : ℕ) := (Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)
  apply (Finset.card_le_card ?_).trans (Finset.card_biUnion_le (s := S) (t := roots))
  intro n hn
  obtain ⟨hnI, p, hpS, hval⟩ := Finset.mem_filter.mp hn
  obtain ⟨hpI, hp⟩ := Finset.mem_filter.mp hpS
  have hbig := block_lt_prime_power hp (Finset.mem_Ioc.mp hpI).1 hk
  exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ((Finset.mem_Ico.mp hnI).2.trans hbig), hval⟩⟩
end RootCounts
theorem main : H1 → H2 → OMA.E978R2.H2 := by
  classical
  intro hlocal htail f hi hd
  dsimp only
  intro A hA
  let k := f.natDegree - 2
  obtain ⟨N₁, h₁⟩ := hlocal f hi hd (2 * A) (by omega)
  obtain ⟨N₂, h₂⟩ := htail f hi hd (2 * A) (by omega)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  let S := (Finset.Ioc N.sqrt N).filter Nat.Prime
  let middle := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let far := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let hits := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ N.sqrt < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have hm : 2 * A * middle.card < N :=
    (Nat.mul_le_mul_left _ (intermediate_hits_le_total_roots f N k (by dsimp [k]; omega))).trans_lt
      (h₁ N ((le_max_left N₁ N₂).trans hN))
  have hf : 2 * A * far.card < N := h₂ N ((le_max_right N₁ N₂).trans hN)
  have cover : hits ⊆ middle ∪ far := by
    intro n hn
    obtain ⟨hnI, p, hp, hroot, hval⟩ := Finset.mem_filter.mp hn
    by_cases hcut : p ≤ N
    · have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hroot, hcut⟩, hp⟩
      exact Finset.mem_union.mpr (.inl <| Finset.mem_filter.mpr ⟨hnI, p, hpS, hval⟩)
    · exact Finset.mem_union.mpr (.inr <| Finset.mem_filter.mpr
        ⟨hnI, p, hp, Nat.lt_of_not_ge hcut, hval⟩)
  have hcount := Nat.mul_le_mul_left A
    ((Finset.card_le_card cover).trans (Finset.card_union_le middle far))
  change A * hits.card < N
  nlinarith only [hm, hf, hcount]
end OMA.E978R3
end S3

section SL1
namespace OMA.L1
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
theorem h1_proof : OMA.E978R1.H1 := by
  intro f hi hd
  dsimp only
  intro hadm
  obtain ⟨D, Y₀, _, hD⟩ := Erdos978RootCount.eventual_bound f hi hd
  exact Erdos978LocalSieve.local_density_from_root_bound f (f.natDegree - 2) (by omega) hadm ⟨D, Y₀, hD⟩
end OMA.L1
end SL1

section SL2
namespace OMA.L2
namespace Erdos978RootCount
open Polynomial
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
theorem h2_h1_proof : OMA.E978R2.H1 := by
  intro f hi hd
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
end OMA.L2
end SL2

section SL3
namespace OMA.L3
open Filter
open scoped Classical
namespace Erdos978RootCount
open Polynomial
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
namespace Erdos978Intermediate
lemma prime_count_sublinear (A : ℕ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, A * N.primeCounting < N := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hπ : ∀ᶠ n : ℕ in atTop,
      (n.primeCounting : ℝ) ≤ (Real.log 4 + 1) * (n : ℝ) / Real.log n := by
    simpa using hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  have hlog : ∀ᶠ n : ℕ in atTop, (A : ℝ) * (Real.log 4 + 1) < Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp hcast).eventually_gt_atTop _
  apply eventually_atTop.mp
  filter_upwards [hπ, hlog, eventually_gt_atTop 1] with n hπn hlogn hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hupper := mul_le_mul_of_nonneg_left ((le_div_iff₀ hp).mp hπn) (Nat.cast_nonneg A : 0 ≤ (A : ℝ))
  have hlower := mul_lt_mul_of_pos_right hlogn (lt_trans zero_lt_one hn1)
  have hstrict : ((A : ℝ) * n.primeCounting) * Real.log n < (n : ℝ) * Real.log n := by
    nlinarith only [hupper, hlower]
  exact_mod_cast (lt_of_mul_lt_mul_right hstrict hp.le)
end Erdos978Intermediate
open Erdos978RootCount Erdos978Intermediate in
theorem h2_h2_h1_proof : OMA.E978R3.H1 := by
  classical
  intro f hi hd
  dsimp only
  intro A hA
  let k := f.natDegree - 2
  obtain ⟨D, Y₀, _, hroots⟩ := eventual_bound f hi hd
  obtain ⟨N₀, hsmall⟩ := prime_count_sublinear (A * D)
  refine ⟨max N₀ (Y₀ * Y₀), ?_⟩
  intro N hN
  let S := (Finset.Ioc N.sqrt N).filter Nat.Prime
  let count (p : ℕ) := ((Finset.range (p ^ k)).filter fun (r : ℕ) =>
    (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card
  have hsqrt : Y₀ ≤ N.sqrt := Nat.le_sqrt.mpr ((le_max_right _ _).trans hN)
  have hcard : S.card ≤ N.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp hI).2, hprime⟩
  have hsum : (∑ p ∈ S, count p) ≤ N.primeCounting * D := calc
    _ ≤ ∑ _p ∈ S, D := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
      exact hroots p hprime (hsqrt.trans_lt (Finset.mem_Ioc.mp hI).1)
    _ = S.card * D := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcard
  change A * (∑ p ∈ S, count p) < N
  calc
    _ ≤ A * (N.primeCounting * D) := Nat.mul_le_mul_left _ hsum
    _ = (A * D) * N.primeCounting := by ring
    _ < _ := hsmall N ((le_max_left _ _).trans hN)
end OMA.L3
end SL3

section SL4
section
namespace OAI
open Filter Asymptotics
open scoped Topology
namespace QuarticPowerFree
open Polynomial
open scoped BigOperators Count
noncomputable def dyadicTailCount (f : Polynomial ℤ) (k M : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc M (2 * M)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ M < p ∧ (p : ℤ)^k ∣ f.eval (n : ℤ)).card
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
open MvPolynomial Finsupp MonomialOrder
open scoped MonomialOrder
variable {σ K : Type*} [Field K]
def q_221 (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (d : σ →₀ ℕ) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ d
theorem q_493 (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, p-r ∈ I ∧
      (∀ d ∈ r.support, q_221 m I d) ∧ m.degree r ≼[m] m.degree p := by
  classical
  let b : {q : MvPolynomial σ K // q ∈ I ∧ q ≠ 0} → MvPolynomial σ K := Subtype.val
  have hb : ∀ i, IsUnit (m.leadingCoeff (b i)) := by
    intro i
    apply isUnit_iff_ne_zero.mpr
    exact m.leadingCoeff_ne_zero_iff.mpr i.property.2
  obtain ⟨g, r, hpr, hdeg, hr⟩ := m.div hb p
  have hg : Finsupp.linearCombination _ b g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ i.property.1
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [hpr, add_sub_cancel_right]; exact hg
  · intro d hd q hq hq0
    exact hr d hd ⟨q, hq, hq0⟩
  · have hlin : m.degree (Finsupp.linearCombination _ b g) ≼[m] m.degree p := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply m.degree_sum_le.trans
      apply Finset.sup_le
      intro i _
      simpa [smul_eq_mul, mul_comm] using hdeg i
    have heq : r = p - Finsupp.linearCombination _ b g := by rw [hpr]; ring
    rw [heq]
    exact (m.degree_sub_le).trans (max_le le_rfl hlin)
theorem q_227 (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) (hp : ∀ d ∈ p.support, q_221 m I d)
    (hI : p ∈ I) : p = 0 := by
  by_contra hp0
  exact hp _ (m.degree_mem_support hp0) p hI hp0 le_rfl
theorem q_108 [Finite σ] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ s : Finset (σ →₀ ℕ),
      (∀ d ∈ s, ∃ p ∈ I, p ≠ 0 ∧ m.degree p = d) ∧
      ∀ d, q_221 m I d ↔ ∀ a ∈ s, ¬ a ≤ d := by
  classical
  let D : Set (σ →₀ ℕ) := {d | ∃ p ∈ I, p ≠ 0 ∧ m.degree p = d}
  have hf : {a | Minimal (· ∈ D) a}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  refine ⟨hf.toFinset, ?_, ?_⟩
  · intro d hd
    exact (hf.mem_toFinset.mp hd).1
  · intro d
    constructor
    · intro hn a ha had
      obtain ⟨p, hp, hp0, he⟩ := (hf.mem_toFinset.mp ha).1
      exact hn p hp hp0 (he ▸ had)
    · intro hn p hp hp0 hpd
      have hpD : m.degree p ∈ D := ⟨p, hp, hp0, rfl⟩
      obtain ⟨a, hap, ha⟩ := (show D.IsPWO from Set.isPWO_of_wellQuasiOrderedLE D).exists_le_minimal hpD
      exact hn a (hf.mem_toFinset.mpr ha) (hap.trans hpd)
noncomputable def q_5 (T : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {d | d.degree ≤ T}
@[simp] theorem mem_totalSpace {T : ℕ} {p : MvPolynomial σ K} :
    p ∈ q_5 T ↔ p.totalDegree ≤ T := by
  simp only [q_5, mem_restrictSupport_iff, totalDegree, Finset.sup_le_iff]
  rfl
noncomputable def q_287 (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (T : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {d | q_221 m I d ∧ d.degree ≤ T}
theorem q_474 (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (T : ℕ) : q_287 m I T ≤ q_5 T := by
  intro p hp d hd
  exact (hp hd).2
theorem q_401 [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (T : ℕ) :
    (q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap =
      (q_287 degLex I T).map (Ideal.Quotient.mkₐ K I).toLinearMap := by
  apply le_antisymm
  · rintro y ⟨p, hp, rfl⟩
    obtain ⟨r, hr, hn, hd⟩ := q_493 degLex I p
    refine ⟨r, ?_, ?_⟩
    · intro d hdr
      refine ⟨hn d hdr, ?_⟩
      exact (le_totalDegree hdr).trans
        ((degLex_totalDegree_monotone hd).trans (mem_totalSpace.mp hp))
    · apply Ideal.Quotient.eq.mpr
      simpa only [neg_sub] using I.neg_mem hr
  · exact Submodule.map_mono (q_474 _ _ _)
theorem q_116 [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (T : ℕ) :
    Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {d : σ →₀ ℕ // q_221 degLex I d ∧ d.degree ≤ T} := by
  rw [q_401]
  let M := q_287 degLex I T
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict M
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    apply Subtype.ext
    exact q_227 degLex I p.val (fun d hd => (p.property hd).1)
      (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  have heq : LinearMap.range f = M.map (Ideal.Quotient.mkₐ K I).toLinearMap :=
    LinearMap.range_domRestrict _ _
  rw [← heq, LinearMap.finrank_range_of_inj hf]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)
open scoped BigOperators
noncomputable def q_277 (h N : ℕ) : Finset (Fin h → ℕ) :=
  (Finset.range (N+1)).biUnion (Finset.Nat.antidiagonalTuple h)
@[simp] theorem mem_simplexTuple {h N : ℕ} (x : Fin h → ℕ) :
    x ∈ q_277 h N ↔ ∑ i, x i ≤ N := by
  classical
  simp only [q_277, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro hx; exact ⟨_, by omega, rfl⟩
private theorem q_434 (h N : ℕ) :
    (Finset.Nat.antidiagonalTuple h N).card = h.multichoose N := by
  classical
  have hc := Finset.card_finsuppAntidiag_nat_eq_multichoose
    (s := (Finset.univ : Finset (Fin h))) N
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  apply Finset.card_bij (fun x _ => Finsupp.equivFunOnFinite.symm x)
  · intro x hx
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa [Finsupp.sum_fintype] using Finset.Nat.mem_antidiagonalTuple.mp hx,
      Finset.subset_univ _⟩
  · intro x _ y _ he
    exact Finsupp.equivFunOnFinite.symm.injective he
  · intro x hx
    refine ⟨Finsupp.equivFunOnFinite x, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag'.mp hx).1
theorem q_497 (h N : ℕ) :
    (q_277 h N).card = (N+h).choose h := by
  classical
  rw [q_277, Finset.card_biUnion]
  · simp_rw [q_434]
    exact Nat.sum_range_multichoose N h
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hi).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hj))
noncomputable def q_78 (n T : ℕ) : Finset (Fin n →₀ ℕ) :=
  (q_277 n T).map Finsupp.equivFunOnFinite.symm.toEmbedding
@[simp] theorem mem_simplexExponents {n T : ℕ} (d : Fin n →₀ ℕ) :
    d ∈ q_78 n T ↔ d.degree ≤ T := by
  classical
  simp only [q_78, Finset.mem_map_equiv, mem_simplexTuple]
  change (∑ i, d i) ≤ T ↔ (d.sum fun _ e => e) ≤ T
  rw [Finsupp.sum_fintype]
  intro i; rfl
@[simp] theorem card_simplexExponents (n T : ℕ) :
    (q_78 n T).card = (T+n).choose n := by
  rw [q_78, Finset.card_map, q_497]
noncomputable def q_18 {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (T : ℕ) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (q_78 n T).filter (fun d => ∀ a ∈ s, ¬ a ≤ d)
@[simp] theorem mem_normalExponents {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (T : ℕ)
    (d : Fin n →₀ ℕ) :
    d ∈ q_18 s T ↔ d.degree ≤ T ∧ ∀ a ∈ s, ¬ a ≤ d := by
  classical
  simp [q_18]
@[simp] theorem normalExponents_empty (n T : ℕ) :
    q_18 (∅ : Finset (Fin n →₀ ℕ)) T = q_78 n T := by
  classical
  ext; simp
noncomputable def q_142 {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) := by
  classical
  exact s.image (fun b => b-a)
theorem q_430 {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) : (q_142 a s).card ≤ s.card := by
  classical
  exact Finset.card_image_le
theorem q_312 {n : ℕ} (a b d : Fin n →₀ ℕ) :
    b-a ≤ d ↔ b ≤ a+d := by
  simp only [Finsupp.le_def, Finsupp.tsub_apply, Finsupp.add_apply]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega
theorem q_144 {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) (T : ℕ) (ha : a.degree ≤ T) :
    (q_18 (insert a s) T).card +
      (q_18 (q_142 a s) (T-a.degree)).card =
        (q_18 s T).card := by
  classical
  have hs : q_18 (insert a s) T =
      (q_18 s T).filter (fun d => ¬ a ≤ d) := by
    ext d; simp [and_left_comm, and_comm]
  have hc : ((q_18 s T).filter (a ≤ ·)).card =
      (q_18 (q_142 a s) (T-a.degree)).card := by
    symm
    apply Finset.card_bij (fun d _ => a+d)
    · intro d hd
      obtain ⟨hdT, hdS⟩ := (mem_normalExponents _ _ d).mp hd
      apply Finset.mem_filter.mpr
      refine ⟨(mem_normalExponents _ _ _).mpr ⟨?_, ?_⟩, le_add_right le_rfl⟩
      · rw [map_add]; omega
      · intro b hb hbad
        exact hdS (b-a) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
          ((q_312 a b d).mpr hbad)
    · intro d _ e _ h; exact add_left_cancel h
    · intro d hd
      obtain ⟨hdS, had⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdT, hdN⟩ := (mem_normalExponents _ _ d).mp hdS
      refine ⟨d-a, (mem_normalExponents _ _ _).mpr ⟨?_, ?_⟩,
        add_tsub_cancel_of_le had⟩
      · have he := congrArg Finsupp.degree (add_tsub_cancel_of_le had)
        simp only [map_add] at he
        omega
      · intro b hb hbd
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
        apply hdN c hc
        have h := (q_312 a c (d-a)).mp hbd
        simpa only [add_tsub_cancel_of_le had] using h
  rw [hs, ← hc, add_comm]
  exact Finset.card_filter_add_card_filter_not _
theorem q_156 {n : ℕ} (s : Finset (Fin n →₀ ℕ)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      ((q_18 s T).card : ℚ) = P.eval (T : ℚ) := by
  classical
  suffices H : ∀ N, ∀ s : Finset (Fin n →₀ ℕ), s.card = N →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
        ((q_18 s T).card : ℚ) = P.eval (T : ℚ) by
    exact H s.card s rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro s hs
    by_cases he : s = ∅
    · subst s
      refine ⟨Polynomial.preHilbertPoly ℚ n 0,
        (Polynomial.natDegree_preHilbertPoly _ _ _).le, 0, ?_⟩
      intro T _
      rw [normalExponents_empty, card_simplexExponents,
        Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
      simp
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
      let s' := s.erase a
      have ht : s'.card < N := by rw [← hs]; exact Finset.card_erase_lt_of_mem ha
      obtain ⟨P, hP, TP, hPT⟩ := ih s'.card ht s' rfl
      obtain ⟨Q, hQ, TQ, hQT⟩ := ih (q_142 a s').card
        ((q_430 _ _).trans_lt ht) _ rfl
      refine ⟨P - Q.comp (Polynomial.X - Polynomial.C (a.degree : ℚ)), ?_,
        max TP (TQ+a.degree), ?_⟩
      · apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le hP
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
        exact hQ
      · intro T hT
        have hTP : TP ≤ T := (le_max_left _ _).trans hT
        have hTQ : TQ+a.degree ≤ T := (le_max_right _ _).trans hT
        have haT : a.degree ≤ T := by omega
        have hh := q_144 a s' T haT
        rw [show insert a s' = s from Finset.insert_erase ha] at hh
        have hhQ : ((q_18 s T).card : ℚ) +
            ((q_18 (q_142 a s') (T-a.degree)).card : ℚ) =
              ((q_18 s' T).card : ℚ) := by exact_mod_cast hh
        rw [hPT T hTP, hQT (T-a.degree) (by omega)] at hhQ
        rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        rw [Nat.cast_sub haT] at hhQ
        linarith
theorem q_52 {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ) := by
  classical
  obtain ⟨s, _, hs⟩ := q_108 degLex I
  have hc (T : ℕ) :
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
        (q_18 s T).card := by
    rw [q_116, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, hs, and_comm]
  obtain ⟨P, hP, T₀, hT⟩ := q_156 s
  refine ⟨P, hP, T₀, ?_⟩
  intro T h
  rw [hc]
  exact hT T h
theorem q_336 (m : MonomialOrder σ)
    (p : MvPolynomial σ K) (hp : p ≠ 0) (d : σ →₀ ℕ) :
    q_221 m (Ideal.span {p}) d ↔ ¬ m.degree p ≤ d := by
  constructor
  · intro h
    exact h p (Ideal.subset_span (Set.mem_singleton p)) hp
  · intro h q hq hq0 hqd
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    have hr : r ≠ 0 := by intro he; simp [he] at hq0
    rw [m.degree_mul hp hr] at hqd
    exact h ((_root_.le_add_right le_rfl).trans hqd)
theorem q_337 {n : ℕ} (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (T : ℕ) (hT : p.totalDegree ≤ T) :
    Module.finrank K ((q_5 T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) +
        (T-p.totalDegree+n).choose n = (T+n).choose n := by
  classical
  have hc : Module.finrank K ((q_5 T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) =
      (q_18 {degLex.degree p} T).card := by
    rw [q_116, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, q_336 degLex p hp,
      Finset.mem_singleton, forall_eq, and_comm]
  rw [hc]
  have hh := q_144 (degLex.degree p) ∅ T
    (by simpa only [degree_degLexDegree] using hT)
  simpa [q_142, degree_degLexDegree] using hh
theorem q_416 (n e T : ℕ) (he : e ≤ T) :
    (T-e+(n+1)).choose (n+1) +
      ∑ j ∈ Finset.range e, (T-j+n).choose n =
        (T+(n+1)).choose (n+1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    have hi := ih (by omega)
    have hE : T-e+n = (T-(e+1)+(n+1)) := by omega
    have hE' : T-e+(n+1) = (T-e+n)+1 := by omega
    have hb := Nat.choose_succ_succ (T-e+n) n
    change (T-e+n+1).choose (n+1) = (T-e+n).choose n + (T-e+n).choose (n+1) at hb
    rw [← hE'] at hb
    rw [← hE]
    omega
noncomputable def q_24 (n e : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range e, Polynomial.preHilbertPoly ℚ n j
theorem q_63 (n e : ℕ) :
    (q_24 n e).coeff n = (e : ℚ)/(n.factorial : ℚ) := by
  simp [q_24, Polynomial.coeff_preHilbertPoly_self, div_eq_mul_inv]
theorem q_90 (n e : ℕ) :
    (q_24 n e).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_preHilbertPoly _ _ _).le
theorem q_111 {n : ℕ} (p : MvPolynomial (Fin (n+1)) K)
    (hp : p ≠ 0) (T : ℕ) (hT : p.totalDegree ≤ T) :
    (Module.finrank K ((q_5 T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) : ℚ) =
        (q_24 n p.totalDegree).eval (T : ℚ) := by
  have hh := q_337 p hp T hT
  have hb := q_416 n p.totalDegree T hT
  have he : Module.finrank K ((q_5 T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) =
        ∑ j ∈ Finset.range p.totalDegree, (T-j+n).choose n := by omega
  rw [he, Nat.cast_sum]
  simp only [q_24, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ ((Finset.mem_range.mp hj).le.trans hT)]
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
section
open Polynomial Filter
open scoped Topology
theorem q_39 (P : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in atTop, 0 ≤ P.eval (T : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_cases hd : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd] at hP ⊢
    simpa only [eval_C, leadingCoeff_C, eventually_const] using hP
  · by_contra hl
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) (le_of_not_ge hl)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℚ)) atTop atTop)
    have hn := ht.eventually_lt_atBot 0
    obtain ⟨T, hT, hT'⟩ := (hP.and hn).exists
    exact (not_lt_of_ge hT) hT'
theorem q_47 (P Q : Polynomial ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h) (hQ : Q.natDegree ≤ h)
    (hle : ∀ᶠ T : ℕ in atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ)) :
    P.coeff h ≤ Q.coeff h := by
  have hn : 0 ≤ (Q-P).leadingCoeff :=
    q_39 (Q-P)
      (hle.mono (fun T hT => by simpa only [eval_sub, sub_nonneg] using hT))
  have hd : (Q-P).natDegree ≤ h := (natDegree_sub_le _ _).trans (max_le hQ hP)
  have hc : 0 ≤ (Q-P).coeff h := by
    rcases hd.eq_or_lt with he | he
    · simpa only [← he, coeff_natDegree] using hn
    · rw [coeff_eq_zero_of_natDegree_lt he]
  simpa only [coeff_sub, sub_nonneg] using hc
theorem q_6 (P Q : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in atTop, 0 ≤ P.eval (T : ℚ))
    (hle : ∀ᶠ T : ℕ in atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hh
  have hdeg : Q.natDegree < P.natDegree := lt_of_not_ge hh
  have hP0 : P ≠ 0 := by intro he; simp [he] at hdeg
  have hl : 0 < P.leadingCoeff := lt_of_le_of_ne
    (q_39 P hP)
    (Ne.symm (leadingCoeff_ne_zero.mpr hP0))
  have hm := q_39 (Q-P)
    (hle.mono (fun T hT => by simpa only [eval_sub, sub_nonneg] using hT))
  rw [leadingCoeff_sub_of_degree_lt' (degree_lt_degree hdeg)] at hm
  linarith
end
open MvPolynomial Finsupp MonomialOrder
open scoped MonomialOrder BigOperators
def q_100 {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (J : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ¬ a.support ⊆ J
theorem q_473 {n : ℕ} {s : Finset (Fin n →₀ ℕ)}
    {J : Finset (Fin n)} (hJ : q_100 s J)
    (d : Fin n →₀ ℕ) (hd : d.support ⊆ J) : ∀ a ∈ s, ¬ a ≤ d := by
  intro a ha had
  apply hJ a ha
  intro i hi
  apply hd
  apply Finsupp.mem_support_iff.mpr
  have hai : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hh := had i
  omega
theorem q_425 {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (B : ℕ) (hB : ∀ a ∈ s, a.degree < B)
    (d : Fin n →₀ ℕ) (hd : ∀ a ∈ s, ¬ a ≤ d) :
    q_100 s (Finset.univ.filter (fun i => B ≤ d i)) := by
  classical
  intro a ha hsub
  apply hd a ha
  intro i
  by_cases hi : i ∈ a.support
  · have hh : B ≤ d i := (Finset.mem_filter.mp (hsub hi)).2
    exact ((Finsupp.le_degree i a).trans (hB a ha).le).trans hh
  · simpa only [Finsupp.notMem_support_iff.mp hi] using Nat.zero_le (d i)
theorem q_243 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ d, q_221 degLex I d ↔ ∀ a ∈ s, ¬ a ≤ d)
    (J : Finset (Fin n)) (hJ : q_100 s J) :
    AlgebraicIndependent K (fun j : J => Ideal.Quotient.mk I (X j.val)) := by
  classical
  let f := (Ideal.Quotient.mkₐ K I).comp (rename (fun j : J => j.val))
  have he : MvPolynomial.aeval (fun j : J => Ideal.Quotient.mk I (X j.val)) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f]
  rw [algebraicIndependent_iff_injective_aeval, he]
  intro p q hpq
  apply sub_eq_zero.mp
  apply (rename_injective (fun j : J => j.val) Subtype.val_injective)
  rw [map_zero]
  apply q_227 degLex I
  · intro d hd
    apply (hs d).mpr
    apply q_473 hJ
    intro i hi
    have hv := support_subset_vars_of_mem_support hd hi
    have hr := vars_rename (fun j : J => j.val) (p-q) hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact j.property
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (p-q) = 0
    rw [map_sub, hpq, sub_self]
noncomputable def q_61 {n : ℕ} (B T : ℕ) (J : Finset (Fin n)) :
    Finset (Fin n → ℕ) := by
  classical
  exact Fintype.piFinset (fun i => Finset.range (if i ∈ J then T+1 else B))
theorem q_294 {n : ℕ} (B T h : ℕ) (hB : 1 ≤ B)
    (J : Finset (Fin n)) (hJ : J.card ≤ h) :
    (q_61 B T J).card ≤ B^n * (T+1)^h := by
  classical
  rw [q_61, Fintype.card_piFinset]
  simp only [Finset.card_range]
  rw [Finset.prod_ite]
  have he : (Finset.univ.filter (fun i : Fin n => i ∈ J)) = J := by ext; simp
  rw [he]
  simp only [Finset.prod_const]
  have hc : (Finset.univ.filter (fun i : Fin n => i ∉ J)).card ≤ n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    (T+1)^J.card * B^(Finset.univ.filter (fun i : Fin n => i ∉ J)).card ≤
        (T+1)^h * B^n := Nat.mul_le_mul
          (Nat.pow_le_pow_right (by omega) hJ) (Nat.pow_le_pow_right hB hc)
    _ = B^n * (T+1)^h := Nat.mul_comm _ _
theorem q_302 {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (h : ℕ) (hh : ∀ J, q_100 s J → J.card ≤ h) (T : ℕ) :
    (q_18 s T).card ≤
      (2^n * (s.sup Finsupp.degree + 1)^n) * (T+1)^h := by
  classical
  let B := s.sup Finsupp.degree + 1
  let faces := (Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.card ≤ h)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBs : ∀ a ∈ s, a.degree < B := by
    intro a ha
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Finsupp.degree) ha)
  have hc : (q_18 s T).image (fun d : Fin n →₀ ℕ => (d : Fin n → ℕ)) ⊆
      faces.biUnion (q_61 B T) := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    have ha' := mem_normalExponents s T a |>.mp ha
    let J := Finset.univ.filter (fun i => B ≤ a i)
    refine Finset.mem_biUnion.mpr ⟨J, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        hh J (q_425 s B hBs a ha'.2)⟩
    · rw [q_61, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      by_cases hi : i ∈ J
      · rw [if_pos hi]
        exact Nat.lt_succ_of_le ((Finsupp.le_degree i a).trans ha'.1)
      · rw [if_neg hi]
        have hh : ¬ B ≤ a i := by simpa [J] using hi
        omega
  have hf : faces.card ≤ 2^n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    (q_18 s T).card =
      ((q_18 s T).image (fun d : Fin n →₀ ℕ => (d : Fin n → ℕ))).card :=
        (Finset.card_image_of_injective _ (fun p q h => Finsupp.ext (fun i => congrFun h i))).symm
    _ ≤ (faces.biUnion (q_61 B T)).card := Finset.card_le_card hc
    _ ≤ ∑ J ∈ faces, (q_61 B T J).card := Finset.card_biUnion_le
    _ ≤ faces.card * (B^n * (T+1)^h) := by
      simpa only [nsmul_eq_mul, Nat.cast_id] using Finset.sum_le_card_nsmul faces
        (fun J => (q_61 B T J).card) (B^n * (T+1)^h)
        (fun J hJ => q_294 B T h hB J (Finset.mem_filter.mp hJ).2)
    _ ≤ 2^n * (B^n * (T+1)^h) := Nat.mul_le_mul_right _ hf
    _ = (2^n * (s.sup Finsupp.degree+1)^n) * (T+1)^h := by rw [Nat.mul_assoc]
theorem q_70 {n : ℕ} {K : Type*} [Field K] (T : ℕ) :
    Module.Finite K (q_5 (σ := Fin n) (K := K) T) := by
  classical
  let e : {d : Fin n →₀ ℕ // d.degree ≤ T} ≃ {d // d ∈ q_78 n T} :=
    Equiv.subtypeEquivRight (fun d => (mem_simplexExponents d).symm)
  let : Finite {d : Fin n →₀ ℕ | d.degree ≤ T} :=
    Finite.of_equiv {d // d ∈ q_78 n T} e.symm
  exact Module.Finite.of_basis (basisRestrictSupport K {d : Fin n →₀ ℕ | d.degree ≤ T})
theorem q_353 {n : ℕ} {K : Type*} [Field K] (T : ℕ) :
    Module.finrank K (q_5 (σ := Fin n) (K := K) T) = (T+n).choose n := by
  change Module.finrank K (restrictSupport K {d : Fin n →₀ ℕ | d.degree ≤ T}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  rw [← card_simplexExponents n T, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun d => (mem_simplexExponents d).symm)
theorem q_87 {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a)))) (T : ℕ) :
    (T+h).choose h ≤
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := q_70 (n := n) (K := K) T
  let f := (Ideal.Quotient.mkₐ K I).comp (rename j)
  have hf : Function.Injective f := by
    rw [algebraicIndependent_iff_injective_aeval] at hj
    have he : MvPolynomial.aeval (fun a => Ideal.Quotient.mk I (X (j a))) = f := by
      apply algHom_ext
      intro a
      simp [f]
    rwa [he] at hj
  let g : q_5 (σ := Fin h) (K := K) T →ₗ[K]
      (q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap :=
    (f.toLinearMap.domRestrict (q_5 T)).codRestrict _ (by
      intro p
      exact ⟨rename j p.val,
        mem_totalSpace.mpr ((totalDegree_rename_le j p.val).trans (mem_totalSpace.mp p.property)),
        rfl⟩)
  have hg : Function.Injective g := by
    intro p q he
    exact Subtype.ext (hf (congrArg Subtype.val he))
  rw [← q_353 (K := K) (n := h) T]
  exact LinearMap.finrank_le_finrank_of_injective hg
theorem q_362 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤)
    (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ d ∈ s, ∃ p ∈ I, p ≠ 0 ∧ degLex.degree p = d) :
    q_100 s ∅ := by
  classical
  intro a ha hh
  have ha0 : a = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hh)
  obtain ⟨p, hp, hp0, hd⟩ := hs a ha
  have he := (degLex.degree_eq_zero_iff (f := p)).mp (hd.trans ha0)
  have hu : IsUnit (degLex.leadingCoeff p) := isUnit_iff_ne_zero.mpr
    (degLex.leadingCoeff_ne_zero_iff.mpr hp0)
  exact hI (I.eq_top_of_isUnit_mem hp (he ▸ hu.map C))
theorem q_59 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) :
    ∃ P : Polynomial ℚ, ∃ j : Fin P.natDegree → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) ∧
      (P.natDegree.factorial : ℚ)⁻¹ ≤ P.coeff P.natDegree ∧
      ∃ T₀ : ℕ, ∀ T ≥ T₀,
        (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
          P.eval (T : ℚ) := by
  classical
  obtain ⟨s, hsI, hs⟩ := q_108 degLex I
  let faces := (Finset.univ : Finset (Fin n)).powerset.filter (q_100 s)
  have hne : faces.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, q_362 I hI s hsI⟩⟩
    exact Finset.mem_powerset.mpr (Finset.empty_subset _)
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image faces Finset.card hne
  have hfree : q_100 s J := (Finset.mem_filter.mp hJ).2
  have hmax' (J' : Finset (Fin n)) (hJ' : q_100 s J') : J'.card ≤ J.card :=
    hmax J' (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hJ'⟩)
  let j : Fin J.card → Fin n := fun a => ((Finset.equivFin J).symm a).val
  have hj : Function.Injective j := Subtype.val_injective.comp (Finset.equivFin J).symm.injective
  have hind : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) :=
    (q_243 I s hs J hfree).comp _ (Finset.equivFin J).symm.injective
  obtain ⟨P, _, T₀, hT⟩ := q_52 I
  have hcount (T : ℕ) :
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
        (q_18 s T).card := by
    rw [q_116, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, hs, and_comm]
  let c := 2^n * (s.sup Finsupp.degree+1)^n
  let Q : Polynomial ℚ := Polynomial.C (c : ℚ) *
    (Polynomial.X + Polynomial.C 1)^J.card
  have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h]
    positivity
  have hPQ : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h, hcount]
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X]
    exact_mod_cast q_302 s J.card hmax' T
  have hupper : P.natDegree ≤ J.card := by
    apply (q_6 P Q hPnonneg hPQ).trans
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, zero_add]
    exact Polynomial.natDegree_pow_le.trans (by simp only [Polynomial.natDegree_X_add_C, mul_one]; exact le_rfl)
  have hlower : ∀ᶠ T : ℕ in Filter.atTop,
      (Polynomial.preHilbertPoly ℚ J.card 0).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h, Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    exact_mod_cast q_87 I j hind T
  have hbase : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (Polynomial.preHilbertPoly ℚ J.card 0).eval (T : ℚ) := by
    apply Filter.Eventually.of_forall
    intro T
    rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    positivity
  have hdegree : P.natDegree = J.card := by
    apply Nat.le_antisymm hupper
    simpa only [Polynomial.natDegree_preHilbertPoly] using
      q_6 _ P hbase hlower
  have hcoeff : (J.card.factorial : ℚ)⁻¹ ≤ P.coeff J.card := by
    have hh := q_47
      (Polynomial.preHilbertPoly ℚ J.card 0) P J.card
      (by rw [Polynomial.natDegree_preHilbertPoly]) hupper hlower
    simpa only [Polynomial.coeff_preHilbertPoly_self] using hh
  refine ⟨P, ?_⟩
  rw [hdegree]
  exact ⟨j, hj, hind, hcoeff, T₀, hT⟩
theorem q_441 {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (J : Ideal (MvPolynomial (Fin m) K)) (j : Fin m → Fin n)
    (hker : ∀ p, Ideal.Quotient.mk I (rename j p) = 0 ↔ p ∈ J) (T : ℕ) :
    Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := q_70 (n := n) (K := K) T
  let f₀ := (Ideal.Quotient.mkₐ K I).comp (rename j)
  let f := Ideal.Quotient.liftₐ J f₀ (fun p hp => (hker p).mpr hp)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro y hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (hker p).mp hy
  let g := (f.toLinearMap.domRestrict
    ((q_5 T).map (Ideal.Quotient.mkₐ K J).toLinearMap)).codRestrict
      ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) (by
        rintro ⟨y, p, hp, rfl⟩
        exact ⟨rename j p,
          mem_totalSpace.mpr ((totalDegree_rename_le j p).trans (mem_totalSpace.mp hp)), rfl⟩)
  apply LinearMap.finrank_le_finrank_of_injective (f := g)
  intro y z he
  exact Subtype.ext (hf (congrArg Subtype.val he))
theorem q_91 {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (j : Fin (h+1) → Fin n) :
    ¬ AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) := by
  intro hj
  have hlower : ∀ᶠ T : ℕ in Filter.atTop,
      (Polynomial.preHilbertPoly ℚ (h+1) 0).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    apply hT.mono
    intro T h
    rw [← h, Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    exact_mod_cast q_87 I j hj T
  have hbase : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (Polynomial.preHilbertPoly ℚ (h+1) 0).eval (T : ℚ) := by
    apply Filter.Eventually.of_forall
    intro T
    rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    positivity
  have hh := q_6 _ P hbase hlower
  rw [Polynomial.natDegree_preHilbertPoly] at hh
  omega
theorem q_211 {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (j : Fin (h+1) → Fin n)
    (q : MvPolynomial (Fin (h+1)) K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename j p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h := by
  have hh : ∀ᶠ T : ℕ in Filter.atTop,
      (q_24 h q.totalDegree).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    filter_upwards [hT, Filter.eventually_ge_atTop q.totalDegree] with T hT hqT
    rw [← hT, ← q_111 q hq T hqT]
    exact_mod_cast q_441 I (Ideal.span {q}) j
      (fun p => (hker p).trans Ideal.mem_span_singleton.symm) T
  have hcoeff := q_47
    (q_24 h q.totalDegree) P h
    (q_90 _ _) hP hh
  rw [q_63] at hcoeff
  have hf : (0 : ℚ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  exact (div_le_iff₀ hf).mp hcoeff |>.trans_eq (mul_comm _ _)
open Polynomial
theorem q_292 {R S : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S]
    (f : R →+* S) (p : R) (hp : p ≠ 0) (hfp : f p = 0) :
    ∃ g : R, Irreducible g ∧ f g = 0 := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hp rfl).elim
  | unit u hu => exact (hu.map f).ne_zero hfp |>.elim
  | mul a i ha hi ih =>
    rw [map_mul, mul_eq_zero] at hfp
    rcases hfp with h | h
    · exact ⟨i, hi, h⟩
    · exact ih ha h
theorem q_298 {R F L : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L]
    (x : L) (p : Polynomial R) (hp : p ≠ 0) (hpx : Polynomial.aeval x p = 0) :
    ∃ g : Polynomial R, Irreducible g ∧ g.IsPrimitive ∧ g.natDegree ≠ 0 ∧
      (∀ q : Polynomial R, Polynomial.aeval x q = 0 ↔ g ∣ q) := by
  obtain ⟨g, hg, hxg⟩ := q_292 (Polynomial.aeval x).toRingHom p hp hpx
  change Polynomial.aeval x g = 0 at hxg
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    change Function.Injective ((algebraMap F L) ∘ (algebraMap R F))
    exact (RingHom.injective (algebraMap F L)).comp (IsFractionRing.injective R F)
  have hn : g.natDegree ≠ 0 := by
    intro h
    have he := eq_C_of_natDegree_eq_zero h
    have hh := hxg
    rw [he, Polynomial.aeval_C] at hh
    have hz : g.coeff 0 = 0 := hinj (hh.trans (map_zero _).symm)
    exact hg.ne_zero (he.trans (by rw [hz, Polynomial.C_0]))
  have hprim := hg.isPrimitive hn
  have hi : Irreducible (g.map (algebraMap R F)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hx : Polynomial.aeval x (g.map (algebraMap R F)) = 0 := by
    simpa only [Polynomial.aeval_map_algebraMap] using hxg
  have ha : IsAlgebraic F x := ⟨g.map (algebraMap R F), hi.ne_zero, hx⟩
  have hass := (minpoly.irreducible ha.isIntegral).associated_of_dvd hi (minpoly.dvd F x hx)
  refine ⟨g, hg, hprim, hn, ?_⟩
  intro q
  constructor
  · intro hq
    apply (hprim.dvd_iff_fraction_map_dvd_fraction_map F).mpr
    apply hass.dvd_iff_dvd_left.mp
    exact minpoly.dvd F x (by simpa only [Polynomial.aeval_map_algebraMap] using hq)
  · rintro ⟨r, rfl⟩
    simp only [map_mul, hxg, zero_mul]
open MvPolynomial in
theorem q_267 {h : ℕ} {K L : Type*} [Field K] [Field L]
    [Algebra K L] (y : Fin h → L) (hy : AlgebraicIndependent K y) (x : L)
    (p : MvPolynomial (Fin (h+1)) K) (hp : p ≠ 0)
    (hpx : MvPolynomial.aeval (Fin.cases x y) p = 0) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, MvPolynomial.aeval (Fin.cases x y) r = 0 ↔ q ∣ r) := by
  let R := MvPolynomial (Fin h) K
  let F := FractionRing R
  let f : R →ₐ[K] L := MvPolynomial.aeval y
  have hf : Function.Injective f := algebraicIndependent_iff_injective_aeval.mp hy
  let : Algebra R L := f.toRingHom.toAlgebra
  let : Algebra F L := (IsFractionRing.lift (K := F) hf).toAlgebra
  have hcomp : algebraMap R L = (algebraMap F L).comp (algebraMap R F) := by
    apply RingHom.ext
    intro a
    exact (IsFractionRing.lift_algebraMap (K := F) (g := f.toRingHom) hf a).symm
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq' hcomp
  let E := finSuccEquiv K h
  have heval (r : MvPolynomial (Fin (h+1)) K) :
      Polynomial.aeval x (E r) = MvPolynomial.aeval (Fin.cases x y) r := by
    have he : (Polynomial.aeval x).toRingHom.comp E.toRingHom =
        (MvPolynomial.aeval (Fin.cases x y)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.C c)) = _
        rw [finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C]
        change MvPolynomial.aeval y (MvPolynomial.C c) =
          MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.C c)
        simp only [MvPolynomial.aeval_C]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.X 0)) = _
          rw [finSuccEquiv_X_zero, Polynomial.aeval_X]
          change x = MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.X (0 : Fin (h+1)))
          simp only [MvPolynomial.aeval_X, Fin.cases_zero]
        · change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.X j.succ)) = _
          rw [finSuccEquiv_X_succ, Polynomial.aeval_C]
          change MvPolynomial.aeval y (MvPolynomial.X j) =
            MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.X j.succ)
          simp only [MvPolynomial.aeval_X, Fin.cases_succ]
    exact congrArg (fun g : MvPolynomial (Fin (h+1)) K →+* L => g r) he
  have hep : E p ≠ 0 := by
    intro hh
    exact hp (E.injective (hh.trans (map_zero E).symm))
  obtain ⟨g, hg, _, hgn, hgker⟩ := q_298 (F := F) x (E p) hep
    ((heval p).trans hpx)
  refine ⟨E.symm g, ?_, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff E.symm).mpr hg
  · simpa only [← natDegree_finSuccEquiv, E, AlgEquiv.apply_symm_apply] using hgn
  · intro r
    rw [← heval r, hgker]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨E.symm s, ?_⟩
      apply E.injective
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using hs
    · rintro ⟨s, rfl⟩
      exact ⟨E s, by simp only [map_mul, AlgEquiv.apply_symm_apply]⟩
theorem q_440 {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin m → Fin n) :
    MvPolynomial.aeval (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) =
      (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.rename j) := by
  ext a
  simp
theorem q_149 {h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (x : A) (y : Fin h → A) (hy : AlgebraicIndependent K y)
    (hxy : ¬ AlgebraicIndependent K (Fin.cases x y)) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, MvPolynomial.aeval (Fin.cases x y) r = 0 ↔ q ∣ r) := by
  let L := FractionRing A
  let e : A →ₐ[K] L := IsScalarTower.toAlgHom K A L
  have he : Function.Injective e := IsFractionRing.injective A L
  have hcase : Fin.cases (e x) (fun a => e (y a)) =
      fun a : Fin (h+1) => e (Fin.cases x y a) := by
    funext a
    exact Fin.cases rfl (fun _ => rfl) a
  have hei (r : MvPolynomial (Fin (h+1)) K) :
      MvPolynomial.aeval (Fin.cases (e x) (fun a => e (y a))) r =
        e (MvPolynomial.aeval (Fin.cases x y) r) := by
    rw [hcase, ← MvPolynomial.comp_aeval_apply]
  have hyL : AlgebraicIndependent K (fun a => e (y a)) := hy.map' he
  rw [algebraicIndependent_iff] at hxy
  push Not at hxy
  obtain ⟨p, hpx, hp⟩ := hxy
  obtain ⟨q, hq, hqdeg, hqker⟩ := q_267
    (fun a => e (y a)) hyL (e x) p hp (by rw [hei, hpx, map_zero])
  refine ⟨q, hq, hqdeg, fun r => ?_⟩
  rw [← hqker, hei, map_eq_zero_iff e he]
theorem q_356 {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))))
    (i : Fin n)
    (hdep : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (Fin.cases i j a)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename (Fin.cases i j) r) = 0 ↔ q ∣ r) := by
  have hcase : Fin.cases (Ideal.Quotient.mk I (MvPolynomial.X i))
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) =
        fun a : Fin (h+1) => Ideal.Quotient.mk I (MvPolynomial.X (Fin.cases i j a)) := by
    funext a
    exact Fin.cases rfl (fun _ => rfl) a
  have hd : ¬ AlgebraicIndependent K
      (Fin.cases (Ideal.Quotient.mk I (MvPolynomial.X i))
        (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a)))) := by
    rwa [hcase]
  obtain ⟨q, hq, hqdeg, hqker⟩ := q_149
    (Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) hj hd
  refine ⟨q, hq, hqdeg, fun r => ?_⟩
  rw [← hqker, hcase, q_440]
  rfl
theorem q_458 {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (z : Fin (h+1) → Fin n)
    (hz : AlgebraicIndependent K
      (fun a : Fin h => Ideal.Quotient.mk I (MvPolynomial.X (z a.succ))))
    (hdep : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (z a)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename z r) = 0 ↔ q ∣ r) := by
  have he (a : Fin (h+1)) : Fin.cases (z 0) (fun b : Fin h => z b.succ) a = z a :=
    Fin.cases rfl (fun _ => rfl) a
  have hd : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X
        (Fin.cases (z 0) (fun b : Fin h => z b.succ) a))) := by
    simpa only [he] using hdep
  obtain ⟨q, hq, hqd, hker⟩ := q_356 I (fun a => z a.succ) hz (z 0) hd
  refine ⟨q, hq, hqd, fun r => ?_⟩
  have hr : MvPolynomial.rename z r =
      MvPolynomial.rename (fun a => Fin.cases (z 0) (fun b : Fin h => z b.succ) a) r :=
    congrArg (fun v : Fin (h+1) → Fin n => MvPolynomial.rename v r) (funext he).symm
  rw [hr]
  exact hker r
theorem q_145 {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : Fin (h+1) → Fin n)
    (hz : AlgebraicIndependent K
      (fun a : Fin h => Ideal.Quotient.mk I (MvPolynomial.X (z a.succ)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename z r) = 0 ↔ q ∣ r) := by
  have hd := q_91 I P hP hT z
  obtain ⟨q, hq, hqdeg, hker⟩ := q_458 I z hz hd
  exact ⟨q, hq, hqdeg,
    q_211 I P hP hT z q hq.ne_zero hker, hker⟩
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
namespace QuarticPowerFree
section
open scoped Classical
theorem q_255 {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) (h : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs : ∀ m ∈ (MvPolynomial.pderiv i p).support,
      m.sum (fun _ e => e) < p.totalDegree := by
    intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hc
    have hp : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul]))
    have hh := MvPolynomial.le_totalDegree hp
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (by rfl)] at hh
    exact hh
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr h
  have hpos : 0 < p.totalDegree := (Nat.zero_le _).trans_lt (hs m hm)
  exact (Finset.sup_lt_iff hpos).mpr hs
theorem q_482 {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) :
    (MvPolynomial.pderiv i p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨m, hm, hjm⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  refine (MvPolynomial.mem_vars_iff_mem_support j).mpr
    ⟨m + Finsupp.single i 1,
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul])), ?_⟩
  rw [Finsupp.mem_support_iff, Finsupp.add_apply]
  have hh := Finsupp.mem_support_iff.mp hjm
  omega
theorem q_328 {σ K : Type*} [CommRing K]
    [IsDomain K] [CharZero K] (i : σ) (p : MvPolynomial σ K)
    (hi : i ∈ p.vars) : MvPolynomial.pderiv i p ≠ 0 := by
  classical
  obtain ⟨m, hm, him⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
  have hcoeff : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  intro h
  have hh := congrArg (fun polynomial => polynomial.coeff (m - Finsupp.single i 1)) h
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hmi,
    MvPolynomial.coeff_zero] at hh
  have hnat : ∀ n : ℕ, (n : K) + 1 ≠ 0 := by
    intro n
    exact_mod_cast Nat.succ_ne_zero n
  exact (mul_ne_zero hcoeff (hnat _)) hh
theorem q_141 {σ K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val))
    (p : MvPolynomial σ K) (hp : (p.vars : Set σ) ⊆ J)
    (hz : MvPolynomial.aeval z p = 0) : p = 0 := by
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (fun j : J => j.val) Subtype.val_injective (by simpa using hp)
  subst p
  rw [MvPolynomial.aeval_rename] at hz
  have hh : q = 0 := (algebraicIndependent_iff_injective_aeval.mp hJ)
    (hz.trans (map_zero _).symm)
  simp [hh]
theorem q_179 {σ K F : Type*}
    [Field K] [CharZero K] [CommRing F] [Algebra K F]
    (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val))
    (i : σ) (p : MvPolynomial σ K) (hp : p ≠ 0)
    (hvars : (p.vars : Set σ) ⊆ insert i J) (hz : MvPolynomial.aeval z p = 0) :
    ∃ q : MvPolynomial σ K, q ≠ 0 ∧ (q.vars : Set σ) ⊆ insert i J ∧
      q.totalDegree ≤ p.totalDegree ∧ MvPolynomial.aeval z q = 0 ∧
      MvPolynomial.aeval z (MvPolynomial.pderiv i q) ≠ 0 := by
  classical
  let S : Set (MvPolynomial σ K) :=
    {q | q ≠ 0 ∧ (q.vars : Set σ) ⊆ insert i J ∧ MvPolynomial.aeval z q = 0}
  have hpS : p ∈ S := ⟨hp, hvars, hz⟩
  let q := Function.argminOn MvPolynomial.totalDegree S ⟨p, hpS⟩
  have hq : q ∈ S := Function.argminOn_mem _ _ _
  have hiq : i ∈ q.vars := by
    by_contra hn
    apply hq.1
    apply q_141 z J hJ q _ hq.2.2
    intro j hj
    rcases hq.2.1 hj with he | he
    · exact False.elim (hn (he ▸ hj))
    · exact he
  have hder : MvPolynomial.pderiv i q ≠ 0 := q_328 i q hiq
  have hdeg := q_255 i q hder
  refine ⟨q, hq.1, hq.2.1, ?_, hq.2.2, ?_⟩
  · exact Function.argminOn_le _ _ hpS
  · intro he
    have hdS : MvPolynomial.pderiv i q ∈ S :=
      ⟨hder, fun j hj => hq.2.1 (q_482 i q hj), he⟩
    exact Function.not_lt_argminOn MvPolynomial.totalDegree S hdS hdeg
theorem q_191 {σ K F : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K] [CommRing F] [IsDomain F] [Algebra K F]
    (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val)) (D : ℕ)
    (hrel : ∀ i : ↥(Jᶜ), ∃ p : MvPolynomial σ K, p ≠ 0 ∧
      (p.vars : Set σ) ⊆ insert i.val J ∧ p.totalDegree ≤ D ∧
      MvPolynomial.aeval z p = 0) :
    ∃ G : ↥(Jᶜ) → MvPolynomial σ K,
      (∀ i, (G i).totalDegree ≤ D) ∧
      (∀ i, MvPolynomial.aeval z (G i) = 0) ∧
      Matrix.det (fun i j : ↥(Jᶜ) => MvPolynomial.aeval z
        (MvPolynomial.pderiv j.val (G i))) ≠ 0 := by
  classical
  have hh : ∀ i : ↥(Jᶜ), ∃ q : MvPolynomial σ K,
      (q.vars : Set σ) ⊆ insert i.val J ∧ q.totalDegree ≤ D ∧
      MvPolynomial.aeval z q = 0 ∧
      MvPolynomial.aeval z (MvPolynomial.pderiv i.val q) ≠ 0 := by
    intro i
    obtain ⟨p, hp, hv, hd, he⟩ := hrel i
    obtain ⟨q, _, hvq, hdq, heq, hder⟩ :=
      q_179 z J hJ i.val p hp hv he
    exact ⟨q, hvq, hdq.trans hd, heq, hder⟩
  choose G hvars hdeg heval hder using hh
  refine ⟨G, hdeg, heval, ?_⟩
  have hmat : (fun i j : ↥(Jᶜ) => MvPolynomial.aeval z
      (MvPolynomial.pderiv j.val (G i))) =
      Matrix.diagonal (fun i : ↥(Jᶜ) => MvPolynomial.aeval z
        (MvPolynomial.pderiv i.val (G i))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars, map_zero]
      intro hj
      rcases hvars i hj with hj | hj
      · exact hij (Subtype.ext hj.symm)
      · exact j.property hj
  rw [hmat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hder i)
theorem q_150 {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field F] (A : Matrix α β F)
    (hA : Submodule.span F (Set.range A) = ⊤) :
    ∃ a : β → α, Function.Injective a ∧ Matrix.det (fun i j => A (a i) j) ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F A
  let := Fintype.ofInjective a ha
  let b : Module.Basis κ F (β → F) := Module.Basis.mk hli (by rw [hspan, hA])
  have hcard : Fintype.card β = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := F), Module.finrank_eq_card_basis b]
  let e : β ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_row
  exact hli.comp e e.injective
noncomputable def q_88 {σ β K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (v : β → σ) :
    MvPolynomial σ K →ₗ[K] (β → F) :=
  LinearMap.pi (fun j => (MvPolynomial.aeval z).toLinearMap.comp
    (MvPolynomial.pderiv (v j)).toLinearMap)
theorem q_460 {σ α β K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (v : β → σ)
    (G : α → MvPolynomial σ K) (p : MvPolynomial σ K)
    (hp : p ∈ Submodule.span K (Set.range G)) :
    q_88 z v p ∈ Submodule.span F
      (Set.range (fun i => q_88 z v (G i))) := by
  let W := Submodule.span F (Set.range (fun i => q_88 z v (G i)))
  have hs : Submodule.span K (Set.range G) ≤
      (W.restrictScalars K).comap (q_88 z v) := by
    apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  exact hs hp
theorem q_180 {σ α β K F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field K] [Field F] [Algebra K F]
    (z : σ → F) (v : β → σ) (G : α → MvPolynomial σ K)
    (P : β → MvPolynomial σ K)
    (hP : ∀ i, P i ∈ Submodule.span K (Set.range G))
    (hdet : Matrix.det (fun i j => MvPolynomial.aeval z
      (MvPolynomial.pderiv (v j) (P i))) ≠ 0) :
    ∃ a : β → α, Function.Injective a ∧
      Matrix.det (fun i j => MvPolynomial.aeval z
        (MvPolynomial.pderiv (v j) (G (a i)))) ≠ 0 := by
  classical
  let A : Matrix β β F := fun i => q_88 z v (P i)
  have hli : LinearIndependent F A := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have htop : Submodule.span F (Set.range A) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_fintype_fun_eq_card (R := F)).symm
  apply q_150 (fun i => q_88 z v (G i))
  apply top_unique
  rw [← htop]
  apply Submodule.span_le.mpr
  rintro q ⟨i, rfl⟩
  exact q_460 z v G (P i) (hP i)
end
open MvPolynomial
open scoped Classical
theorem q_390 {n h D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : (h.factorial : ℚ) * P.coeff h ≤ D)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a)))) :
    ∃ J : Set (Fin n), Nat.card J = h ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) K,
        (∀ i, (G i).totalDegree ≤ D) ∧ (∀ i, G i ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (G i)) ∉ I := by
  classical
  let z : Fin n → MvPolynomial (Fin n) K ⧸ I := fun a => Ideal.Quotient.mk I (X a)
  have hjj : Function.Injective j := by
    intro a b hab
    exact hj.injective (congrArg (fun x => Ideal.Quotient.mk I (X x)) hab)
  obtain ⟨J, hJr⟩ : ∃ J : Set (Fin n), Set.range j = J := ⟨_, rfl⟩
  have hmem (a : Fin n) : a ∈ Set.range j ↔ a ∈ J := Set.ext_iff.mp hJr a
  let e : Fin h ≃ J := (Equiv.ofInjective j hjj).trans (Equiv.setCongr hJr)
  have heval (a : Fin h) : (e a).val = j a := rfl
  have hej (a : J) : j (e.symm a) = a.val := (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply a))
  have hJ : AlgebraicIndependent K (fun a : J => z a.val) := by
    have hh := hj.comp e.symm e.symm.injective
    simpa only [Function.comp_def, hej, z] using hh
  have hae : aeval z = Ideal.Quotient.mkₐ K I := by ext a; simp only [aeval_X]; rfl
  have hr : ∀ i : ↥(Jᶜ), ∃ p : MvPolynomial (Fin n) K, p ≠ 0 ∧
      (p.vars : Set (Fin n)) ⊆ insert i.val J ∧ p.totalDegree ≤ D ∧ aeval z p = 0 := by
    intro i
    let v : Fin (h+1) → Fin n := Fin.cases i.val j
    have hvj : AlgebraicIndependent K
        (fun a : Fin h => Ideal.Quotient.mk I (X (v a.succ))) := hj
    obtain ⟨q,hq,_,hd,hker⟩ := q_145 I P hP hT v hvj
    have hvi : Function.Injective v := by
      intro a b hab
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ b => exact False.elim (i.property ((hmem i.val).mp (Set.mem_range.mpr ⟨b,hab.symm⟩)))
      | succ a =>
        cases b using Fin.cases with
        | zero => exact False.elim (i.property ((hmem i.val).mp (Set.mem_range.mpr ⟨a,hab⟩)))
        | succ b => exact congrArg Fin.succ (hjj hab)
    refine ⟨rename v q, (rename_injective v hvi).ne hq.ne_zero, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b,_,rfl⟩ := mem_vars_rename v q ha
      cases b using Fin.cases with
      | zero => exact Set.mem_insert _ _
      | succ b => exact Set.mem_insert_of_mem _ ((hmem (j b)).mp (Set.mem_range_self b))
    · apply (totalDegree_rename_le v q).trans
      exact_mod_cast hd.trans hD
    · rw [hae]
      exact (hker q).mpr (dvd_refl q)
  obtain ⟨G,hdeg,hvan,hdet⟩ := q_191 z J hJ D hr
  refine ⟨J, ?_, G,hdeg,?_,?_⟩
  · exact (Nat.card_congr e.symm).trans (Nat.card_fin h)
  · intro i
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [hae, Ideal.Quotient.mkₐ_eq_mk] using hvan i)
  · have hdet' : Matrix.det (fun i l : ↥(Jᶜ) => Ideal.Quotient.mk I (pderiv l.val (G i))) ≠ 0 := by
      simpa only [hae, Ideal.Quotient.mkₐ_eq_mk] using hdet
    intro hm
    apply hdet'
    let M : Matrix ↥(Jᶜ) ↥(Jᶜ) (MvPolynomial (Fin n) K) := fun i l => pderiv l.val (G i)
    have hm0 : Ideal.Quotient.mk I M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have he : ((Ideal.Quotient.mk I).mapMatrix M).det = 0 :=
      ((Ideal.Quotient.mk I).map_det M).symm.trans hm0
    exact he
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
def q_13 {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) : Matrix β β R :=
  (B * B.transpose).det • 1 - B.transpose * (B * B.transpose).adjugate * B
theorem q_376 {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) :
    B * q_13 B = 0 := by
  unfold q_13
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.one_mul, sub_self]
theorem q_160 {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R)
    (x : β → R) (hx : B *ᵥ x = 0) :
    q_13 B *ᵥ x = (B * B.transpose).det • x := by
  unfold q_13
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]
theorem q_161 {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (B : Matrix α β F) (hB : LinearIndependent F B) :
    (B * B.transpose).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hz : B.transpose *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec] at hker
    have hh := congrArg (fun y => dotProduct x y) hker
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at hh
    exact hh
  apply hx
  have hinj : Function.Injective (fun x => x ᵥ* B) :=
    Matrix.vecMul_injective_iff.mpr hB
  apply hinj
  simpa only [Matrix.mulVec_transpose, Matrix.zero_vecMul] using hz
theorem q_242 {α β γ F : Type*}
    [Fintype β] [CommSemiring F] [Fintype γ]
    (A : Matrix α β F) (B : Matrix γ β F)
    (hspan : ∀ i, A i ∈ Submodule.span F (Set.range B))
    (x : β → F) (hx : B *ᵥ x = 0) : A *ᵥ x = 0 := by
  ext i
  change dotProduct (A i) x = 0
  have hsub : Submodule.span F (Set.range B) ≤
      LinearMap.ker ((dotProductBilin F F).flip x) := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact congrFun hx j
  exact hsub (hspan i)
theorem q_148 {α β γ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [CommRing R]
    (A : Matrix γ β R) (B : Matrix α β R)
    (hspan : ∀ i, A i ∈ Submodule.span R (Set.range B)) (j : β) :
    A *ᵥ (fun i => q_13 B i j) = 0 := by
  apply q_242 A B hspan
  have hh := q_376 B
  ext i
  exact congrArg (fun M => M i j) hh
theorem q_158 {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Field F]
    (B : Matrix α β F) (hdet : (B * B.transpose).det ≠ 0)
    (x : β → F) (hx : B *ᵥ x = 0) :
    x ∈ Submodule.span F (Set.range (fun j => fun i => q_13 B i j)) := by
  have heq := q_160 B x hx
  have hmem : q_13 B *ᵥ x ∈
      Submodule.span F (Set.range (fun j => fun i => q_13 B i j)) := by
    rw [Matrix.mulVec_eq_sum]
    apply Submodule.sum_mem
    intro j _
    change (fun i => q_13 B i j * x j) ∈ _
    have hh := Submodule.smul_mem
      (Submodule.span F (Set.range (fun j => fun i => q_13 B i j)))
      (x j) (Submodule.subset_span (Set.mem_range_self j))
    convert hh using 1
    ext i
    exact mul_comm _ _
  rw [heq] at hmem
  exact (Submodule.smul_mem_iff _ hdet).mp hmem
theorem q_214 {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℚ) :
    ∃ r : ℕ, r ≤ Fintype.card β ∧ ∃ a : Fin r → α,
      Function.Injective a ∧ LinearIndependent ℚ (fun i => A (a i)) ∧
      Submodule.span ℚ (Set.range (fun i => A (a i))) =
        Submodule.span ℚ (Set.range A) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ A
  let := Fintype.ofInjective a ha
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, ?_, a ∘ e.symm, ha.comp e.symm.injective, ?_, ?_⟩
  · simpa only [Module.finrank_fintype_fun_eq_card] using hli.fintype_card_le_finrank
  · exact hli.comp e.symm e.symm.injective
  · have hrange : Set.range (fun i => A (a (e.symm i))) = Set.range (A ∘ a) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, congrArg (fun j => A (a j)) (e.symm_apply_apply i)⟩
    simpa only [Function.comp_def, hrange] using hspan
theorem q_188 {α β R S : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [CommRing R] [CommRing S] (f : R →+* S) (B : Matrix α β R) :
    (q_13 B).map f = q_13 (B.map f) := by
  have hadj := f.map_adjugate (B * B.transpose)
  have hdet := f.map_det (B * B.transpose)
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hadj hdet
  unfold q_13
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.smul_apply,
    smul_eq_mul, map_mul]
  rw [hdet]
  have hone : f ((1 : Matrix β β R) i j) = (1 : Matrix β β S) i j := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [hone]
  change _ - ((B.transpose * (B * B.transpose).adjugate * B).map f) i j = _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hadj]
theorem q_99 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]
theorem q_109 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    q_99 (A.map fun x => (x : ℝ)) (fun _ => B) hA
theorem q_125 {α β γ : Type*} [Fintype β]
    (A : Matrix α β ℤ) (B : Matrix β γ ℤ) (H K : ℝ)
    (hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) (hB : ∀ i j, |(B i j : ℝ)| ≤ K)
    (i : α) (j : γ) : |((A * B) i j : ℝ)| ≤ (Fintype.card β : ℝ) * H * K := by
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul]
  calc
    |∑ k, (A i k : ℝ) * (B k j : ℝ)| ≤ ∑ k, |(A i k : ℝ) * (B k j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : β, H * K := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hH
    _ = (Fintype.card β : ℝ) * H * K := by simp [mul_assoc]
def q_11 (n : ℕ) (H : ℝ) : ℝ :=
  (1 + (n : ℝ) ^ 2 * H ^ 2) * (Nat.factorial n : ℝ) *
    (1 + (n : ℝ) * H ^ 2) ^ n
theorem q_305 {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (B : Matrix α β ℤ) (n : ℕ)
    (hα : Fintype.card α ≤ n) (hβ : Fintype.card β ≤ n)
    (H : ℝ) (hH : 1 ≤ H) (hB : ∀ i j, |(B i j : ℝ)| ≤ H) (i j : β) :
    |((q_13 B i j : ℤ) : ℝ)| ≤ q_11 n H := by
  let G := B * B.transpose
  let C : ℝ := 1 + (n : ℝ) * H ^ 2
  let K : ℝ := (Nat.factorial n : ℝ) * C ^ n
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg H)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG : ∀ u v, |(G u v : ℝ)| ≤ C := by
    intro u v
    have hh := q_125 B B.transpose H H hH0 hH0 hB
      (fun i j => hB j i) u v
    apply hh.trans
    have hc : (Fintype.card β : ℝ) ≤ n := by exact_mod_cast hβ
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg H)]
  have hdetbound {A : Matrix α α ℤ} (hA : ∀ u v, |(A u v : ℝ)| ≤ C) :
      |(A.det : ℝ)| ≤ K := by
    apply (q_109 A C hA).trans
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le hα)
      (pow_le_pow_right₀ hC hα) (by positivity) (by positivity)
  have hdet : |(G.det : ℝ)| ≤ K := hdetbound hG
  have hadj : ∀ u v, |(G.adjugate u v : ℝ)| ≤ K := by
    intro u v
    rw [Matrix.adjugate_apply]
    apply hdetbound
    intro a b
    by_cases hav : a = v
    · subst a
      rw [Matrix.updateRow_self]
      by_cases hbu : b = u
      · subst b
        simpa using hC
      · simp [Pi.single_eq_of_ne hbu, zero_le_one.trans hC]
    · rw [Matrix.updateRow_ne hav]
      exact hG a b
  have hb₁ : ∀ u v, |((B.transpose * G.adjugate) u v : ℝ)| ≤
      (Fintype.card α : ℝ) * H * K :=
    q_125 B.transpose G.adjugate H K hH0 hK
      (fun i j => hB j i) hadj
  have hb₂ := q_125 (B.transpose * G.adjugate) B
    ((Fintype.card α : ℝ) * H * K) H (by positivity) hH0 hb₁ hB i j
  have hdiag : |(((G.det • (1 : Matrix β β ℤ)) i j : ℤ) : ℝ)| ≤ K := by
    by_cases hij : i = j
    · subst j
      simpa using hdet
    · simpa [Matrix.one_apply, hij] using hK
  have hαr : (Fintype.card α : ℝ) ≤ n := by exact_mod_cast hα
  have hαnonneg : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hsquare : (Fintype.card α : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    sq_le_sq₀ hαnonneg (Nat.cast_nonneg _) |>.mpr hαr
  unfold q_13
  change |(((G.det • (1 : Matrix β β ℤ)) i j -
    ((B.transpose * G.adjugate * B) i j) : ℤ) : ℝ)| ≤ _
  rw [Int.cast_sub]
  apply (abs_sub _ _).trans
  apply (add_le_add hdiag hb₂).trans
  have hsqbound := mul_le_mul_of_nonneg_right hsquare (mul_nonneg (sq_nonneg H) hK)
  dsimp [q_11, K] at *
  nlinarith
theorem q_140 {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field F] [CharZero F]
    (A : Matrix α β ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    ∃ C : Matrix β β ℤ, A * C = 0 ∧
      (∀ i j, |(C i j : ℝ)| ≤ q_11 (Fintype.card β) H) ∧
      ∀ x : β → F, (A.map (Int.castRingHom F)) *ᵥ x = 0 →
        x ∈ Submodule.span F (Set.range
          (fun j => fun i => (C i j : F))) := by
  classical
  let AQ : Matrix α β ℚ := A.map (Int.castRingHom ℚ)
  obtain ⟨r, hr, a, _ha, hli, hspan⟩ := q_214 AQ
  let B : Matrix (Fin r) β ℤ := fun i => A (a i)
  have hliQ : LinearIndependent ℚ (B.map (Int.castRingHom ℚ)) := hli
  have hdetQ := q_161 _ hliQ
  have hdetInt : (B * B.transpose).det ≠ 0 := by
    intro heq
    apply hdetQ
    have hh := (Int.castRingHom ℚ).map_det (B * B.transpose)
    simpa only [heq, map_zero, RingHom.mapMatrix_apply,
      Matrix.map_mul, Matrix.transpose_map] using hh.symm
  have hdetF : ((B.map (Int.castRingHom F)) *
      (B.map (Int.castRingHom F)).transpose).det ≠ 0 := by
    have hh := (Int.castRingHom F).map_det (B * B.transpose)
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hh
    rw [← hh]
    exact Int.cast_ne_zero.mpr hdetInt
  let C := q_13 B
  refine ⟨C, ?_, ?_, ?_⟩
  · have hmulQ : AQ * q_13 (B.map (Int.castRingHom ℚ)) = 0 := by
      ext i j
      have hh := q_148 AQ (B.map (Int.castRingHom ℚ))
        (fun i => by
          change AQ i ∈ Submodule.span ℚ (Set.range (fun t => AQ (a t)))
          rw [hspan]
          exact Submodule.subset_span (Set.mem_range_self i)) j
      exact congrFun hh i
    ext i j
    apply Int.cast_injective (α := ℚ)
    change ((A * C).map (Int.castRingHom ℚ)) i j = 0
    rw [Matrix.map_mul]
    change (AQ * (q_13 B).map (Int.castRingHom ℚ)) i j = 0
    rw [q_188, hmulQ]
    rfl
  · intro i j
    exact q_305 B (Fintype.card β) (by simpa using hr)
      le_rfl H hH (fun i j => hA (a i) j) i j
  · intro x hx
    have hxB : (B.map (Int.castRingHom F)) *ᵥ x = 0 := by
      ext i
      exact congrFun hx (a i)
    have hmem := q_158 _ hdetF x hxB
    rw [← q_188 (Int.castRingHom F) B] at hmem
    exact hmem
def q_38 {ι : Type*} (a : ι →₀ ℕ) : ℕ := a.sum (fun _ e => e)
noncomputable def q_135 (ι : Type*) [Fintype ι] (t : ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact (Finset.range (t + 1)).biUnion (fun n => Finset.univ.finsuppAntidiag n)
theorem q_120 {ι : Type*} [Fintype ι] {a : ι →₀ ℕ} {t : ℕ} :
    a ∈ q_135 ι t ↔ q_38 a ≤ t := by
  classical
  simp only [q_135, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true, q_38]
  exact ⟨fun ⟨n, hn, heq⟩ => heq ▸ Nat.le_of_lt_succ hn,
    fun h => ⟨a.sum (fun _ e => e), Nat.lt_succ_of_le h, rfl⟩⟩
theorem q_220 (ι : Type*) [Fintype ι] (t : ℕ) :
    (q_135 ι t).card = (t + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  rw [q_135, Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ]
    exact Nat.sum_range_multichoose t (Fintype.card ι)
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro a hi hj
  apply hij
  rw [Finset.mem_finsuppAntidiag'] at hi hj
  exact hi.1.symm.trans hj.1
noncomputable def q_7 {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) : (M → R) →ₗ[R] MvPolynomial σ R where
  toFun c := ∑ m : M, MvPolynomial.monomial m.val (c m)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' r c := by
    change (∑ m : M, MvPolynomial.monomial m.val (r • c m)) =
      r • ∑ m : M, MvPolynomial.monomial m.val (c m)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun m _ => map_smul (MvPolynomial.monomial m.val) r (c m))
theorem q_107 {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (m : M) :
    (q_7 M c).coeff m.val = c m := by
  classical
  change (∑ t : M, MvPolynomial.monomial t.val (c t)).coeff m.val = _
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, ← Subtype.ext_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
theorem q_44 {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (m : σ →₀ ℕ) (hm : m ∉ M) :
    (q_7 M c).coeff m = 0 := by
  classical
  change (∑ t : M, MvPolynomial.monomial t.val (c t)).coeff m = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro t _
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro h
  exact hm (h ▸ t.property)
theorem q_183 {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) :
    (q_7 M c).support ⊆ M := by
  intro m hm
  by_contra h
  exact MvPolynomial.mem_support_iff.mp hm
    (q_44 M c m h)
theorem q_79 {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (p : MvPolynomial σ R) (hp : p.support ⊆ M) :
    q_7 M (fun m => p.coeff m.val) = p := by
  classical
  ext m
  by_cases hm : m ∈ M
  · exact q_107 M _ ⟨m, hm⟩
  · rw [q_44 M _ m hm]
    symm
    by_contra hn
    exact hm (hp (MvPolynomial.mem_support_iff.mpr hn))
theorem q_240 {σ R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (M : Finset (σ →₀ ℕ)) (c : M → R) :
    MvPolynomial.map f (q_7 M c) =
      q_7 M (fun m => f (c m)) := by
  change MvPolynomial.map f (∑ m : M, MvPolynomial.monomial m.val (c m)) = _
  simp [map_sum, MvPolynomial.map_monomial, q_7]
theorem q_112 {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (z : σ → R) :
    MvPolynomial.eval z (q_7 M c) =
      dotProduct (fun m : M => m.val.prod (fun i e => z i ^ e)) c := by
  change MvPolynomial.eval z (∑ m : M, MvPolynomial.monomial m.val (c m)) = _
  simp [MvPolynomial.eval_monomial, dotProduct, mul_comm]
theorem q_217 {σ ι F : Type*}
    [Fintype ι] [Field F] [CharZero F]
    (M : Finset (σ →₀ ℕ)) (z : ι → σ → ℤ) (H : ℝ) (hH : 1 ≤ H)
    (heval : ∀ i (m : M), |((m.val.prod (fun l e => z i l ^ e) : ℤ) : ℝ)| ≤ H) :
    ∃ G : M → MvPolynomial σ ℤ,
      (∀ j, (G j).support ⊆ M) ∧
      (∀ j m, |(((G j).coeff m : ℤ) : ℝ)| ≤ q_11 M.card H) ∧
      (∀ j i, MvPolynomial.eval (z i) (G j) = 0) ∧
      ∀ p : MvPolynomial σ F, p.support ⊆ M →
        (∀ i, MvPolynomial.eval (fun l => (z i l : F)) p = 0) →
        p ∈ Submodule.span F (Set.range (fun j => MvPolynomial.map (Int.castRingHom F) (G j))) := by
  classical
  let A : Matrix ι M ℤ := fun i m => m.val.prod (fun l e => z i l ^ e)
  obtain ⟨C, hAC, hC, hspan⟩ := q_140 (F := F) A H hH heval
  let G : M → MvPolynomial σ ℤ := fun j => q_7 M (fun m => C m j)
  refine ⟨G, (fun j => q_183 M _), ?_, ?_, ?_⟩
  · intro j m
    by_cases hm : m ∈ M
    · change |(((q_7 M (fun t => C t j)).coeff m : ℤ) : ℝ)| ≤ _
      rw [q_107 M _ ⟨m, hm⟩]
      simpa only [Fintype.card_coe] using hC ⟨m, hm⟩ j
    · rw [show (G j).coeff m = 0 from q_44 M _ m hm]
      simp only [Int.cast_zero, abs_zero]
      dsimp [q_11]
      positivity
  · intro j i
    rw [show G j = q_7 M (fun m => C m j) from rfl,
      q_112]
    exact congrArg (fun B => B i j) hAC
  · intro p hp hpz
    have hcast : A.map (Int.castRingHom F) =
        (fun i m => m.val.prod (fun l e => (z i l : F) ^ e) : Matrix ι M F) := by
      ext i m
      change ((m.val.prod (fun l e => z i l ^ e) : ℤ) : F) = _
      simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow]
    have hker : (A.map (Int.castRingHom F)) *ᵥ (fun m => p.coeff m.val) = 0 := by
      rw [hcast]
      ext i
      change dotProduct (fun m : M => m.val.prod (fun l e => (z i l : F) ^ e))
        (fun m => p.coeff m.val) = 0
      rw [← q_112, q_79 M p hp]
      exact hpz i
    have hh := Submodule.apply_mem_span_image_of_mem_span
      (q_7 (R := F) M) (hspan _ hker)
    rw [q_79 M p hp] at hh
    have hG : (fun j => q_7 (R := F) M (fun i => (C i j : F))) =
        (fun j => MvPolynomial.map (Int.castRingHom F) (G j)) := by
      funext j
      exact (q_240 (Int.castRingHom F) M (fun i => C i j)).symm
    rw [← Set.range_comp] at hh
    change p ∈ Submodule.span F (Set.range (fun j =>
      q_7 (R := F) M (fun i => (C i j : F)))) at hh
    rwa [hG] at hh
theorem q_289 {σ : Type*} (z : σ → ℤ) (m : σ →₀ ℕ)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i, |(z i : ℝ)| ≤ H) (D : ℕ)
    (hD : q_38 m ≤ D) :
    |((m.prod (fun i e => z i ^ e) : ℤ) : ℝ)| ≤ H ^ D := by
  classical
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  rw [Finsupp.prod, Int.cast_prod, Finset.abs_prod]
  simp only [Int.cast_pow, abs_pow]
  calc
    (∏ i ∈ m.support, |(z i : ℝ)| ^ m i) ≤ ∏ i ∈ m.support, H ^ m i :=
      Finset.prod_le_prod (fun i _ => by positivity)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hz i) _)
    _ = H ^ q_38 m := by simp [q_38, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
    _ ≤ H ^ D := pow_le_pow_right₀ hH hD
theorem q_73 {σ ι F : Type*}
    [Fintype σ] [Fintype ι] [Field F] [CharZero F]
    (z : ι → σ → ℤ) (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H)
    (D : ℕ) :
    ∃ G : q_135 σ D → MvPolynomial σ ℤ,
      (∀ j, (G j).totalDegree ≤ D) ∧
      (∀ j m, |(((G j).coeff m : ℤ) : ℝ)| ≤
        q_11 ((D + Fintype.card σ).choose (Fintype.card σ)) (H ^ D)) ∧
      (∀ j i, MvPolynomial.eval (z i) (G j) = 0) ∧
      ∀ p : MvPolynomial σ F, p.totalDegree ≤ D →
        (∀ i, MvPolynomial.eval (fun l => (z i l : F)) p = 0) →
        p ∈ Submodule.span F (Set.range (fun j => MvPolynomial.map (Int.castRingHom F) (G j))) := by
  classical
  obtain ⟨G, hs, hc, he, hspan⟩ := q_217
    (F := F) (q_135 σ D) z (H ^ D) (one_le_pow₀ hH)
    (fun i m => q_289 (z i) m.val H hH (hz i) D
      (q_120.mp m.property))
  refine ⟨G, ?_, ?_, he, ?_⟩
  · intro j
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    exact fun m hm => q_120.mp (hs j hm)
  · simpa only [q_220] using hc
  · intro p hp heval
    apply hspan p _ heval
    intro m hm
    exact q_120.mpr ((MvPolynomial.le_totalDegree hm).trans hp)
end QuarticPowerFree
end OAI
end
section
namespace OAI
universe u
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped Classical
noncomputable def q_385 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    Fin n → FractionRing (MvPolynomial (Fin n) K ⧸ I) :=
  fun i => algebraMap _ _ (Ideal.Quotient.mk I (X i))
theorem q_490 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    aeval (q_385 I) =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I)
        (FractionRing (MvPolynomial (Fin n) K ⧸ I))).comp (Ideal.Quotient.mkₐ K I) := by
  ext i
  simp only [aeval_X, AlgHom.comp_apply]
  rfl
theorem q_122 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) :
    aeval (q_385 I) p = 0 ↔ p ∈ I := by
  rw [q_490]
  change algebraMap (MvPolynomial (Fin n) K ⧸ I)
    (FractionRing (MvPolynomial (Fin n) K ⧸ I)) (Ideal.Quotient.mk I p) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
theorem q_369 {σ β K F : Type*} [Fintype β] [DecidableEq β]
    [CommRing K] [CommRing F] [Algebra K F]
    (z : σ → F) (v : β → σ) (G : β → MvPolynomial σ K) :
    aeval z (Matrix.det (fun i j => pderiv (v j) (G i))) =
      Matrix.det (fun i j => aeval z (pderiv (v j) (G i))) := by
  exact (aeval z).toRingHom.map_det (fun i j => pderiv (v j) (G i))
theorem q_463 {n h D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : (h.factorial : ℚ) * P.coeff h ≤ D)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))))
    (z : ι → Fin n → ℤ) (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    (∃ G : MvPolynomial (Fin n) ℤ,
      G.totalDegree ≤ D ∧
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ q_11 ((D+n).choose n) (H^D)) ∧
      (∀ i, eval (z i) G = 0) ∧ MvPolynomial.map (Int.castRingHom K) G ∉ I) ∨
    (∃ J : Set (Fin n), Nat.card J = h ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) ℤ,
        (∀ i, (G i).totalDegree ≤ D) ∧
        (∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ q_11 ((D+n).choose n) (H^D)) ∧
        (∀ i, MvPolynomial.map (Int.castRingHom K) (G i) ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (MvPolynomial.map (Int.castRingHom K) (G i))) ∉ I) := by
  classical
  obtain ⟨G,hGdeg,hGheight,hGvan,hGspan⟩ :=
    q_73 (F := K) z H hH hz D
  simp only [Fintype.card_fin] at hGheight
  by_cases hGI : ∀ a, MvPolynomial.map (Int.castRingHom K) (G a) ∈ I
  · right
    obtain ⟨J,hJ,P₁,hPdeg,hPI,hPdet⟩ := q_390 I P hP hT hD j hj
    have hspan (i : ↥(Jᶜ)) : P₁ i ∈ Submodule.span K
        (Set.range (fun a => MvPolynomial.map (Int.castRingHom K) (G a))) :=
      hGspan (P₁ i) (hPdeg i) (hzI (P₁ i) (hPI i))
    have hdet : Matrix.det (fun i l : ↥(Jᶜ) =>
        aeval (q_385 I) (pderiv l.val (P₁ i))) ≠ 0 := by
      rw [← q_369]
      exact mt (q_122 I _).mp hPdet
    obtain ⟨a,_,ha⟩ := q_180
      (q_385 I) (fun l : ↥(Jᶜ) => l.val)
      (fun a => MvPolynomial.map (Int.castRingHom K) (G a)) P₁ hspan hdet
    refine ⟨J,hJ,(fun i => G (a i)),(fun i => hGdeg (a i)),
      (fun i => hGheight (a i)),(fun i => hGI (a i)),?_⟩
    intro hm
    apply ha
    rw [← q_369]
    exact (q_122 I _).mpr hm
  · left
    obtain ⟨a,ha⟩ := not_forall.mp hGI
    exact ⟨G a,hGdeg a,hGheight a,hGvan a,ha⟩
end
open MvPolynomial
lemma q_332 {σ : Type*} (m : σ →₀ ℕ) (i : σ) :
    m i ≤ q_38 m := by
  classical
  by_cases hi : i ∈ m.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp only [Finsupp.notMem_support_iff.mp hi, Nat.zero_le]
theorem q_360 {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℤ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hc : ∀ m, |((p.coeff m : ℤ) : ℝ)| ≤ C)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ H) :
    |((eval z p : ℤ) : ℝ)| ≤
      ((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * C * H^D := by
  classical
  have hs : p.support ⊆ q_135 σ D := by
    intro m hm
    exact q_120.mpr ((le_totalDegree hm).trans hp)
  have hcard : p.support.card ≤ (D + Fintype.card σ).choose (Fintype.card σ) := by
    rw [← q_220]
    exact Finset.card_le_card hs
  have hm (m : σ →₀ ℕ) (hm : m ∈ p.support) :
      |((p.coeff m * m.prod (fun i e => z i ^ e) : ℤ) : ℝ)| ≤ C * H^D := by
    rw [Int.cast_mul, abs_mul]
    exact mul_le_mul (hc m)
      (q_289 z m H hH hz D ((le_totalDegree hm).trans hp))
      (abs_nonneg _) hC
  rw [MvPolynomial.eval_eq, Int.cast_sum]
  calc
    |∑ m ∈ p.support, ((p.coeff m * ∏ i ∈ m.support, z i ^ m i : ℤ) : ℝ)| ≤
        ∑ m ∈ p.support, |((p.coeff m * ∏ i ∈ m.support, z i ^ m i : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ p.support, C * H^D := Finset.sum_le_sum hm
    _ = (p.support.card : ℝ) * C * H^D := by simp [mul_assoc]
    _ ≤ ((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * C * H^D := by
      gcongr
theorem q_472 {σ : Type*} (p : MvPolynomial σ ℤ)
    (D : ℕ) (hp : p.totalDegree ≤ D) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ m, |((p.coeff m : ℤ) : ℝ)| ≤ C) (i : σ) (m : σ →₀ ℕ) :
    |(((pderiv i p).coeff m : ℤ) : ℝ)| ≤ (D : ℝ) * C := by
  classical
  rw [coeff_pderiv]
  by_cases hn : p.coeff (m + Finsupp.single i 1) = 0
  · simp only [hn, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have hd : q_38 (m + Finsupp.single i 1) ≤ D :=
      (le_totalDegree (mem_support_iff.mpr hn)).trans hp
    have hex := (q_332 (m + Finsupp.single i 1) i).trans hd
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hex
    rw [Int.cast_mul, abs_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (m i : ℝ) + 1)]
    calc
      _ ≤ C * (D : ℝ) := mul_le_mul (hc _) (by exact_mod_cast hex) (by positivity) hC
      _ = _ := mul_comm _ _
theorem q_184 {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (D : ℕ) (hp : p.totalDegree ≤ D) (i : σ) :
    (pderiv i p).totalDegree ≤ D-1 := by
  by_cases he : pderiv i p = 0
  · simp [he]
  · have hd := q_255 i p he
    omega
theorem q_447 {σ β R : Type*} [Fintype β] [DecidableEq β]
    [CommRing R] (G : β → MvPolynomial σ R) (v : β → σ)
    (D : ℕ) (hG : ∀ i, (G i).totalDegree ≤ D) :
    (Matrix.det (fun i j => pderiv (v j) (G i))).totalDegree ≤
      Fintype.card β * (D-1) := by
  classical
  let M : Matrix β β (MvPolynomial σ R) := fun i j => pderiv (v j) (G i)
  change M.det.totalDegree ≤ _
  rw [Matrix.det_apply]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro e _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i : β, (pderiv (v i) (G (e i))).totalDegree ≤ ∑ _i : β, (D-1) :=
      Finset.sum_le_sum (fun i _ => q_184 _ D (hG _) _)
    _ = Fintype.card β * (D-1) := by simp
theorem q_342 {σ β : Type*}
    [Fintype σ] [Fintype β] [DecidableEq β]
    (G : β → MvPolynomial σ ℤ) (v : β → σ)
    (D : ℕ) (hG : ∀ i, (G i).totalDegree ≤ D)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hc : ∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ C)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ H) :
    |((eval z (Matrix.det (fun i j => pderiv (v j) (G i))) : ℤ) : ℝ)| ≤
      (Fintype.card β).factorial *
        (((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * ((D : ℝ)*C) * H^D)^Fintype.card β := by
  let M : Matrix β β (MvPolynomial σ ℤ) := fun i j => pderiv (v j) (G i)
  change |((eval z M.det : ℤ) : ℝ)| ≤ _
  rw [(eval z).map_det M]
  apply q_109
  intro i j
  apply q_360 _ D
    ((q_184 _ D (hG i) _).trans (Nat.sub_le _ _))
    ((D : ℝ)*C) H (mul_nonneg (Nat.cast_nonneg _) hC) hH
    (q_472 _ D (hG i) C hC (hc i) (v j)) z hz
theorem q_246 {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    ∃ m : ℕ, ∃ j : Fin m → Fin n,
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) ∧
      Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = m := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let x : Fin n → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X i)
  have hx : MvPolynomial.aeval x = Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X]
    rfl
  have hg : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, hx]
    exact (AlgHom.range_eq_top _).mpr Ideal.Quotient.mk_surjective
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A := by
    rw [hg]
    constructor
    intro a
    exact isAlgebraic_algebraMap (R := (⊤ : Subalgebra K A)) ⟨a, trivial⟩
  obtain ⟨t, ht, htb⟩ := exists_isTranscendenceBasis_subset (R := K) (A := A) (Set.range x)
  have htfin : t.Finite := (Set.finite_range x).subset ht
  let : Fintype t := htfin.fintype
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  choose j hj using fun a : Fin (Fintype.card t) => ht (e a).property
  refine ⟨Fintype.card t, j, ?_, ?_⟩
  · have hi := htb.1.comp e e.injective
    simpa only [Function.comp_def, ← hj] using hi
  · rw [← htb.cardinalMk_eq_trdeg, Cardinal.mk_fintype]
theorem q_45 {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) : (P.natDegree : Cardinal) = Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) := by
  obtain ⟨Q,j,_,hj,_,T₀,hQ⟩ := q_59 I Ideal.IsPrime.ne_top'
  have hQN : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        Q.eval (T : ℚ) := Filter.eventually_atTop.mpr ⟨T₀,hQ⟩
  have hPN : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := hT.mono (fun T ht => by
    rw [← ht]; positivity)
  have hQNN : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Q.eval (T : ℚ) := hQN.mono (fun T ht => by
    rw [← ht]; positivity)
  have heval : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) = Q.eval (T : ℚ) := by
    filter_upwards [hT,hQN] with T hp hq
    exact hp.symm.trans hq
  have hPQ : P.natDegree = Q.natDegree := le_antisymm
    (q_6 P Q hPN (heval.mono fun _ ht => ht.le))
    (q_6 Q P hQNN (heval.mono fun _ ht => ht.ge))
  obtain ⟨m, z, hz, hm⟩ := q_246 I
  have h1 : (P.natDegree : Cardinal) ≤ Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) := by
    rw [hPQ]
    simpa using hj.lift_cardinalMk_le_trdeg
  have h2 : m ≤ P.natDegree := by
    by_contra hh
    have hm' : P.natDegree+1 ≤ m := by omega
    let v : Fin (P.natDegree+1) → Fin n := fun a => z (Fin.castLE hm' a)
    exact q_91 I P le_rfl hT v
      (hz.comp (Fin.castLE hm') (Fin.castLE_injective hm'))
  rw [hm] at h1 ⊢
  exact le_antisymm h1 (by exact_mod_cast h2)
theorem q_266 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (T : ℕ) (hT : p.totalDegree ≤ T) :
    Module.finrank K ((q_5 T).map
      (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) +
      Module.finrank K ((q_5 (T-p.totalDegree)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let J := I ⊔ Ideal.span {p}
  let F := (q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let G := (q_5 (T-p.totalDegree)).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let := q_70 (n := n) (K := K) T
  let := q_70 (n := n) (K := K) (T-p.totalDegree)
  let f := (Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left)).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨Ideal.Quotient.mk I p * x.val, by
        obtain ⟨q, hq, hqx⟩ := x.property
        refine ⟨p*q, ?_, ?_⟩
        · apply mem_totalSpace.mpr
          exact (totalDegree_mul p q).trans ((Nat.add_le_add_left (mem_totalSpace.mp hq) _).trans
            (by omega))
        · change Ideal.Quotient.mk I (p*q) = _
          rw [map_mul]
          exact congrArg (fun y => Ideal.Quotient.mk I p * y) hqx⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hpn : Ideal.Quotient.mk I p ≠ 0 := by
    exact fun h => hp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (mul_left_cancel₀ hpn (congrArg Subtype.val h))
  have hgle : LinearMap.range g ≤ LinearMap.ker f := by
    rintro x ⟨y, rfl⟩
    change (Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left))
      (Ideal.Quotient.mk I p * y.val) = 0
    rw [map_mul]
    have hpJ : Ideal.Quotient.mk J p = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_right : Ideal.span {p} ≤ J) (Ideal.subset_span (Set.mem_singleton p))
    change Ideal.Quotient.mk J p * _ = 0
    rw [hpJ, zero_mul]
  have hk : Module.finrank K G ≤ Module.finrank K (LinearMap.ker f) := by
    rw [← LinearMap.finrank_range_of_inj hg]
    exact Submodule.finrank_mono hgle
  have hdim := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = (q_5 T).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext z
    constructor
    · rintro ⟨⟨y, q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨Ideal.Quotient.mk I q, ⟨q, hq, rfl⟩⟩, rfl⟩
  rw [hr] at hdim
  exact (Nat.add_le_add_left hk _).trans_eq hdim
theorem q_397 (P : Polynomial ℚ) (a : ℚ) (n : ℕ)
    (hn : P.natDegree ≤ n) : (Polynomial.taylor a P).coeff n = P.coeff n := by
  obtain h | rfl := lt_or_eq_of_le hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Polynomial.taylor a P) (by simpa using h),
      Polynomial.coeff_eq_zero_of_natDegree_lt h]
  · rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
theorem q_359 (P : Polynomial ℚ) (a : ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h+1) : (P - Polynomial.taylor a P).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub, q_397 P a n (by omega), sub_self]
theorem q_384 (P : Polynomial ℚ) (a : ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h+1) :
    (P - Polynomial.taylor (-a) P).coeff h = a * (h+1) * P.coeff (h+1) := by
  have hn : (Polynomial.hasseDeriv h P).natDegree ≤ 1 :=
    (Polynomial.natDegree_hasseDeriv_le P h).trans (by omega)
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff,
    Polynomial.eq_X_add_C_of_natDegree_le_one hn]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 h, Nat.choose_succ_self_right]
  push_cast
  ring
theorem q_84 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (P Q : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) =
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap))
    (hQ : ∀ᶠ T : ℕ in Filter.atTop, Q.eval (T : ℚ) =
      Module.finrank K ((q_5 T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap))
    (h : ℕ) (hdeg : P.natDegree ≤ h+1) :
    Q.natDegree ≤ h ∧ Q.coeff h ≤ (p.totalDegree : ℚ) * (h+1) * P.coeff (h+1) := by
  let D := P - Polynomial.taylor (-(p.totalDegree : ℚ)) P
  have hD : D.natDegree ≤ h := q_359 P _ h hdeg
  have hn : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Q.eval (T : ℚ) := hQ.mono (fun T hT => by
    rw [hT]; positivity)
  have hl : ∀ᶠ T : ℕ in Filter.atTop, Q.eval (T : ℚ) ≤ D.eval (T : ℚ) := by
    have hs := (Filter.tendsto_sub_atTop_nat p.totalDegree).eventually hP
    filter_upwards [hP, hQ, hs, Filter.eventually_ge_atTop p.totalDegree] with T hPT hQT hPS hT
    have hi := q_266 I p hp T hT
    have hie : (Module.finrank K ((q_5 T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) +
      Module.finrank K ((q_5 (T-p.totalDegree)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
      exact_mod_cast hi
    dsimp [D]
    rw [Polynomial.eval_sub, Polynomial.taylor_eval, ← sub_eq_add_neg,
      ← Nat.cast_sub hT, hPT, hQT, hPS]
    exact le_sub_iff_add_le.mpr hie
  have hdQ := (q_6 Q D hn hl).trans hD
  refine ⟨hdQ, ?_⟩
  have hc := q_47 Q D h hdQ hD hl
  exact hc.trans_eq (q_384 P (p.totalDegree : ℚ) h hdeg)
end QuarticPowerFree
end OAI
end
section
namespace OAI
universe u
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
section
open Algebra
theorem q_282 {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S]
    (p : Ideal R) [p.IsPrime] [p.FiniteHeight]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] : p.height ≤ P.height := by
  obtain ⟨l, hl, hn⟩ := p.exists_ltSeries_length_eq_height
  have hlp : l.last.asIdeal = p := congrArg PrimeSpectrum.asIdeal hl
  have : P.LiesOver l.last.asIdeal := hlp.symm ▸ (inferInstance : P.LiesOver p)
  obtain ⟨L, hL, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have hlength : (L.length : ℕ∞) ≤ Order.height L.last := Order.length_le_height (show L.last ≤ L.last from le_rfl)
  have hh : Order.height L.last = P.height :=
    (congrArg Order.height hlast).trans (PrimeSpectrum.height_eq_orderHeight _).symm
  calc
    p.height = (l.length : ℕ∞) := hn.symm
    _ = (L.length : ℕ∞) := congrArg Nat.cast hL.symm
    _ ≤ P.height := hlength.trans_eq hh
theorem q_303 {K : Type*} [Field K]
    (n : ℕ) (P : Ideal (MvPolynomial (Fin n) K)) [P.IsMaximal] : P.height = n := by
  induction n with
  | zero =>
    have hdim : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] <;> simp [ringKrullDim_eq_zero_of_field]
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := P) Ideal.IsPrime.ne_top'
    rw [hdim] at h
    exact le_antisymm (by exact_mod_cast h) (zero_le)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let Q := P.map e
    have : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := Q.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    have he : Q.height = P.height := e.height_map P
    have hq : Q.LiesOver q := ⟨rfl⟩
    rw [← he, Polynomial.height_eq_height_add_one q Q, ih q, Nat.cast_add, Nat.cast_one]
theorem q_167 {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective g) (hi : g.IsIntegral)
    (P : Ideal A) [P.IsMaximal] : (s : ℕ∞) ≤ P.height := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have : Algebra.IsIntegral R A := ⟨hi⟩
  let p : Ideal R := P.under R
  have : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) P
  rw [← q_303 s p]
  exact q_282 p P
theorem q_311 {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective g) (hi : g.IsIntegral) : trdeg K A = s := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have : Algebra.IsIntegral R A := ⟨hi⟩
  have : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (g.commutes x).symm)
  have h := trdeg_add_eq K R (A := A)
  have hz : trdeg R A = 0 := trdeg_eq_zero_iff.mpr inferInstance
  rw [hz, add_zero] at h
  rw [← h, MvPolynomial.trdeg_of_isDomain]
  simp
theorem q_178 {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal A) [P.IsMaximal] :
    ∃ s : ℕ, trdeg K A = s ∧ (s : ℕ∞) ≤ P.height := by
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K A
  exact ⟨s, q_311 s g hg hi,
    q_167 s g hg hi P⟩
theorem q_200 {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (p : A) (P : Ideal A) [P.IsMaximal]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) : trdeg K A ≤ 1 := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨s, hs, hheight⟩ := q_178 (K := K) P
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) P hP
  rw [hs]
  have hn : s ≤ 1 := by exact_mod_cast hheight.trans hle
  exact_mod_cast hn
open scoped nonZeroDivisors
theorem q_177
    {R A F B : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field F] [CommRing B] [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra A B] [Algebra R B] [Algebra F B]
    [IsScalarTower R A B] [IsScalarTower R F B]
    [IsLocalization (Algebra.algebraMapSubmonoid A R⁰) B]
    (P : Ideal A) [P.IsPrime]
    [FaithfulSMul R (A ⧸ P)] [Algebra.IsAlgebraic R (A ⧸ P)] :
    (P.map (algebraMap A B)).IsMaximal := by
  let M := Algebra.algebraMapSubmonoid A R⁰
  have hdis : Disjoint (M : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨r, hr, rfl⟩ ha
    have hzero : algebraMap R (A ⧸ P) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    exact hr0 ((FaithfulSMul.algebraMap_injective R (A ⧸ P))
      (hzero.trans (map_zero _).symm))
  let Q := P.map (algebraMap A B)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B P inferInstance hdis
  let C := B ⧸ Q
  let f : A →ₐ[R] C := (Ideal.Quotient.mkₐ R Q).comp (IsScalarTower.toAlgHom R A B)
  let g : (A ⧸ P) →ₐ[R] C := Ideal.Quotient.liftₐ P f (by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
  have hnum (a : A) : IsAlgebraic F (f a) := by
    have hr := IsAlgebraic.algHom g (Algebra.IsAlgebraic.isAlgebraic (R := R) (Ideal.Quotient.mk P a))
    exact hr.extendScalars (FaithfulSMul.algebraMap_injective R F)
  have h_alg : Algebra.IsAlgebraic F C := by
    constructor
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨⟨a,s⟩, hs⟩ := IsLocalization.surj M b
    obtain ⟨r, hr, hsr⟩ := s.property
    have hrn : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    have hrF : algebraMap R F r ≠ 0 := by simpa using (IsFractionRing.injective R F).ne hrn
    have hrel : Ideal.Quotient.mk Q b * algebraMap F C (algebraMap R F r) = f a := by
      change Ideal.Quotient.mk Q b * Ideal.Quotient.mk Q (algebraMap F B (algebraMap R F r)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A B, hsr,
        ← map_mul, hs]
      rfl
    have hc : Ideal.Quotient.mk Q b = f a * algebraMap F C (algebraMap R F r)⁻¹ := by
      rw [← hrel, mul_assoc, ← map_mul, mul_inv_cancel₀ hrF, map_one, mul_one]
    rw [hc]
    exact (hnum a).mul (isAlgebraic_algebraMap _)
  have : Algebra.IsIntegral F C := Algebra.IsAlgebraic.isIntegral
  exact Ideal.Quotient.maximal_of_isField Q (isField_of_isIntegral_of_isField' (Field.toIsField F))
open scoped TensorProduct nonZeroDivisors
theorem q_106
    {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : A) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) (s : ℕ)
    (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective ((Ideal.Quotient.mkₐ K P).comp g))
    (hi : ((Ideal.Quotient.mkₐ K P).comp g).IsIntegral) :
    Algebra.trdeg K A ≤ (s : Cardinal) + 1 := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have hga : Function.Injective g := Function.Injective.of_comp hg
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hga
  have : FaithfulSMul R (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective R (A ⧸ P)).mpr hg
  have : Algebra.IsIntegral R (A ⧸ P) := ⟨hi⟩
  have : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (g.commutes x).symm)
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let F := FractionRing R
  let B := F ⊗[R] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid A R⁰
  have hM : M ≤ A⁰ := by
    rintro a ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa using (FaithfulSMul.algebraMap_injective R A).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (IsLocalization.injective B hM)
  let Q := P.map (algebraMap A B)
  have : Q.IsMaximal := q_177 (R := R) (F := F) P
  have hdis : Disjoint (M : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨r, hr, rfl⟩ ha
    have hz : algebraMap R (A ⧸ P) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      ((FaithfulSMul.algebraMap_injective R (A ⧸ P)) (hz.trans (map_zero _).symm))
  have hQP : Q.under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hdis
  have hm : Q ∈ (Ideal.span {algebraMap A B p}).minimalPrimes := by
    rw [← Set.image_singleton, ← Ideal.map_span, IsLocalization.minimalPrimes_map M B]
    simpa only [Set.mem_preimage, hQP] using hP
  have hFB : Algebra.trdeg F B ≤ 1 := q_200
    (algebraMap A B p) Q hm
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq (fun k => by
    rw [IsScalarTower.algebraMap_apply K R B, IsScalarTower.algebraMap_apply K R A,
      IsScalarTower.algebraMap_apply R A B])
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B M
  have hAB := trdeg_add_eq K A (A := B)
  rw [trdeg_eq_zero (R := A) (A := B), add_zero] at hAB
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F R⁰
  have hRF := trdeg_add_eq K R (A := F)
  rw [trdeg_eq_zero (R := R) (A := F), add_zero, MvPolynomial.trdeg_of_isDomain] at hRF
  have hRF' : Algebra.trdeg K F = (s : Cardinal) := by simpa using hRF.symm
  have : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective F B).mpr
    (algebraMap F B).injective
  have hBF := trdeg_add_eq K F (A := B)
  rw [hRF'] at hBF
  rw [hAB, ← hBF]
  exact add_le_add_right hFB _
theorem q_268
    {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : A) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) :
    Algebra.trdeg K A ≤ Algebra.trdeg K (A ⧸ P) + 1 := by
  classical
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K (A ⧸ P)
  choose x hx using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let G : MvPolynomial (Fin s) K →ₐ[K] A := MvPolynomial.aeval x
  have he : (Ideal.Quotient.mkₐ K P).comp G = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [G, AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i
  have hG : Function.Injective ((Ideal.Quotient.mkₐ K P).comp G) := he.symm ▸ hg
  have hI : ((Ideal.Quotient.mkₐ K P).comp G).IsIntegral := he.symm ▸ hi
  rw [q_311 s g hg hi]
  exact q_106 p P hP s G hG hI
end
open MvPolynomial
theorem q_310 {n : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) (hIJ : I ≤ J) (T : ℕ) :
    Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let F := (q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let := q_70 (n := n) (K := K) T
  let f := (Ideal.Quotient.factorₐ K hIJ).toLinearMap.domRestrict F
  have hr : LinearMap.range f = (q_5 T).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext z
    constructor
    · rintro ⟨⟨y,q,hq,rfl⟩,rfl⟩
      exact ⟨q,hq,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨Ideal.Quotient.mk I q,⟨q,hq,rfl⟩⟩,rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_le f
theorem q_219 {n : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes)
    (P S : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ))
    (hS : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) : ℚ) =
        S.eval (T : ℚ)) : P.natDegree ≤ S.natDegree + 1 := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let q := Q.map (Ideal.Quotient.mk I)
  have hIQ : I ≤ Q := le_sup_left.trans hQ.le
  have hq : q ∈ (Ideal.span {Ideal.Quotient.mk I p}).minimalPrimes := by
    rw [← Set.image_singleton, ← Ideal.map_span,
      Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨Q,hQ,rfl⟩
  have : q.IsPrime := hq.isPrime
  have hi := q_268 (K := K) (Ideal.Quotient.mk I p) q hq
  let e : (A ⧸ q) ≃ₐ[K] (MvPolynomial (Fin n) K ⧸ Q) :=
    DoubleQuot.quotQuotEquivQuotOfLEₐ K hIQ
  have he : Algebra.trdeg K (A ⧸ q) = Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ Q) :=
    AlgEquiv.trdeg_eq e
  rw [he, ← q_45 I P hP, ← q_45 Q S hS] at hi
  exact_mod_cast hi
theorem q_355 {n h : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes)
    (P D S : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) = D.eval (T : ℚ))
    (hS : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) : ℚ) = S.eval (T : ℚ))
    (hdeg : P.natDegree = h+1) : S.natDegree = h := by
  have hd := (q_84 I p hp P D (hP.mono fun _ ht => ht.symm)
    (hD.mono fun _ ht => ht.symm) h hdeg.le).1
  have hs : S.natDegree ≤ D.natDegree := by
    apply q_6 S D
    · exact hS.mono fun T ht => ht ▸ (show (0 : ℚ) ≤ Module.finrank K
        ((q_5 T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) from Nat.cast_nonneg _)
    · filter_upwards [hS,hD] with T ht hd
      rw [← ht,← hd]
      exact_mod_cast q_310 (I ⊔ Ideal.span {p}) Q hQ.le T
  have hl := q_219 I Q p hQ P S hP hS
  omega
end QuarticPowerFree
end OAI
end
section
namespace OAI
universe u
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators
theorem q_378 {R ι : Type*} [CommRing R] [Fintype ι]
    (J : Ideal R) (P : ι → Ideal R) (hP : ∀ i, P i ∈ J.minimalPrimes)
    (hPi : Function.Injective P) :
    ∃ b : ι → R, (∀ i, b i ∉ P i) ∧ (∀ i j, i ≠ j → b i ∈ P j) := by
  classical
  have hex : ∀ i j : ι, i ≠ j → ∃ a : R, a ∈ P j ∧ a ∉ P i := by
    intro i j hij
    by_contra hh
    have hji : P j ≤ P i := by
      intro a ha
      by_contra hn
      exact hh ⟨a,ha,hn⟩
    have he : P i = P j := le_antisymm ((hP i).2 (hP j).1 hji) hji
    exact hij (hPi he)
  choose a ha using hex
  let b : ι → R := fun i => ∏ j : {j : ι // i ≠ j}, a i j j.property
  refine ⟨b,?_,?_⟩
  · intro i
    have : (P i).IsPrime := (hP i).isPrime
    simp only [b, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
    intro j
    exact (ha i j j.property).2
  · intro i j hij
    have : (P j).IsPrime := (hP j).isPrime
    exact Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨j,hij⟩,Finset.mem_univ _,(ha i j hij).1⟩
theorem q_247 {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (J : Ideal (MvPolynomial (Fin n) K))
    (P : ι → Ideal (MvPolynomial (Fin n) K)) (hPr : ∀ i, (P i).IsPrime)
    (hJP : ∀ i, J ≤ P i) (b : ι → MvPolynomial (Fin n) K)
    (hb : ∀ i, b i ∉ P i) (hsep : ∀ i j, i ≠ j → b i ∈ P j)
    (B T : ℕ) (hB : ∀ i, (b i).totalDegree ≤ B) :
    (∑ i, Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap)) ≤
      Module.finrank K ((q_5 (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap) := by
  classical
  let V := fun i => (q_5 T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap
  let W := (q_5 (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap
  let f : ∀ i, q_5 (σ := Fin n) (K := K) T →ₗ[K] V i := fun i =>
    { toFun := fun x => ⟨Ideal.Quotient.mk (P i) x.val, ⟨x.val,x.property,rfl⟩⟩
      map_add' := by intros; ext; simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (Ideal.Quotient.mkₐ K (P i)).toLinearMap.map_smul c x.val }
  have hf : ∀ i, LinearMap.range (f i) = ⊤ := by
    intro i
    apply LinearMap.range_eq_top.mpr
    rintro ⟨y,p,hp,hpy⟩
    exact ⟨⟨p,hp⟩,Subtype.ext hpy⟩
  let (i : ι) : Module.Free K (V i) := Module.Free.of_divisionRing K (V i)
  let (i : ι) : Module.Projective K (V i) := Module.Projective.of_free
  choose l hl using fun i => (f i).exists_rightInverse_of_surjective (hf i)
  have hli : ∀ i (x : V i), Ideal.Quotient.mk (P i) (l i x).val = x.val := by
    intro i x
    exact congrArg Subtype.val (LinearMap.congr_fun (hl i) x)
  let L : (∀ i, V i) →ₗ[K] W :=
    { toFun := fun x => ⟨Ideal.Quotient.mk J (∑ i, b i * (l i (x i)).val), by
        refine ⟨∑ i, b i * (l i (x i)).val, ?_, rfl⟩
        apply Submodule.sum_mem
        intro i _
        apply mem_totalSpace.mpr
        exact (totalDegree_mul _ _).trans ((Nat.add_le_add (hB i)
          (mem_totalSpace.mp (l i (x i)).property)).trans_eq (Nat.add_comm B T))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Pi.add_apply, map_add, AddMemClass.coe_add, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp only [Pi.smul_apply, map_smul, SetLike.val_smul, mul_smul_comm,
          ← Finset.smul_sum]
        exact (Ideal.Quotient.mkₐ K J).toLinearMap.map_smul c _ }
  have hL : Function.Injective L := by
    intro x y hxy
    funext i
    have : (P i).IsPrime := hPr i
    apply Subtype.ext
    have hh := congrArg (fun z : W => Ideal.Quotient.factor (hJP i) z.val) hxy
    change Ideal.Quotient.mk (P i) (∑ j, b j * (l j (x j)).val) =
      Ideal.Quotient.mk (P i) (∑ j, b j * (l j (y j)).val) at hh
    have hs (z : ∀ j, V j) : Ideal.Quotient.mk (P i) (∑ j, b j * (l j (z j)).val) =
        Ideal.Quotient.mk (P i) (b i) * (z i).val := by
      rw [map_sum, Finset.sum_eq_single i, map_mul, hli]
      · intro j _ hji
        rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hsep j i hji),zero_mul]
      · simp
    rw [hs, hs] at hh
    exact mul_left_cancel₀ (fun hz => hb i (Ideal.Quotient.eq_zero_iff_mem.mp hz)) hh
  let := q_70 (n := n) (K := K) T
  let := q_70 (n := n) (K := K) (T+B)
  simpa only [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hL
theorem q_248 {n h : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (J : Ideal (MvPolynomial (Fin n) K))
    (P : ι → Ideal (MvPolynomial (Fin n) K)) (hPr : ∀ i, P i ∈ J.minimalPrimes)
    (hPi : Function.Injective P) (D : Polynomial ℚ) (S : ι → Polynomial ℚ)
    (hD : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K J).toLinearMap) : ℚ) = D.eval (T : ℚ))
    (hS : ∀ i, ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap) : ℚ) = (S i).eval (T : ℚ))
    (hdD : D.natDegree ≤ h) (hdS : ∀ i, (S i).natDegree ≤ h) :
    ∑ i, (S i).coeff h ≤ D.coeff h := by
  classical
  obtain ⟨b,hb,hsep⟩ := q_378 J P hPr hPi
  let B := Finset.univ.sup (fun i => (b i).totalDegree)
  have hB : ∀ i, (b i).totalDegree ≤ B := fun i => Finset.le_sup (f := fun i => (b i).totalDegree) (Finset.mem_univ i)
  have hsum : (∑ i, S i).natDegree ≤ h :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => hdS i)
  have hshift : (Polynomial.taylor (B : ℚ) D).natDegree ≤ h := by simpa using hdD
  have hDT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((q_5 (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap) : ℚ) =
        D.eval ((T+B : ℕ) : ℚ) := by
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hD
    exact Filter.eventually_atTop.mpr ⟨N,fun T hT => hN (T+B) (by omega)⟩
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      (∑ i, S i).eval (T : ℚ) ≤ (Polynomial.taylor (B : ℚ) D).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_all.mpr hS,hDT] with T hs hd
    rw [Polynomial.eval_finsetSum,Polynomial.taylor_eval,← Nat.cast_add,← hd]
    simp_rw [← hs]
    exact_mod_cast q_247 J P (fun i => (hPr i).isPrime)
      (fun i => (hPr i).le) b hb hsep B T hB
  have hc := q_47 (∑ i, S i) (Polynomial.taylor (B : ℚ) D)
    h hsum hshift hle
  rw [q_397 D (B : ℚ) h hdD] at hc
  simpa only [Polynomial.finsetSum_coeff] using hc
theorem q_56 (P Q : Polynomial ℚ)
    (he : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) = Q.eval (T : ℚ)) : P = Q := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite N).image (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro _ ⟨T,hT,rfl⟩
  exact hN T hT
noncomputable def q_8 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : Polynomial ℚ :=
  (q_52 I).choose
noncomputable def q_0 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ℕ := (q_8 I).natDegree
noncomputable def q_16 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ℚ :=
  ((q_0 I).factorial : ℚ) * (q_8 I).coeff (q_0 I)
theorem q_3 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ∀ᶠ T : ℕ in Filter.atTop,
    (Module.finrank K ((q_5 T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
      (q_8 I).eval (T : ℚ) := by
  obtain ⟨N,hN⟩ := (q_52 I).choose_spec.2
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩
theorem q_185 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) : 1 ≤ q_16 I := by
  obtain ⟨P,_,_,_,hc,N,hN⟩ := q_59 I hI
  have he : P = q_8 I := by
    apply q_56
    filter_upwards [Filter.eventually_atTop.mpr ⟨N,hN⟩,q_3 I] with T hp hq
    exact hp.symm.trans hq
  rw [he] at hc
  have hf : (0 : ℚ) < ((q_0 I).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  calc
    1 = ((q_0 I).factorial : ℚ) * ((q_0 I).factorial : ℚ)⁻¹ :=
      (mul_inv_cancel₀ hf.ne').symm
    _ ≤ q_16 I := mul_le_mul_of_nonneg_left hc hf.le
theorem q_119 {n h : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hd : q_0 I = h+1) :
    q_0 Q = h :=
  q_355 I Q p hp hQ _ _ _ (q_3 I)
    (q_3 _) (q_3 Q) hd
theorem q_239 {n h : ℕ} {K : Type u} {ι : Type*}
    [Field K] [Fintype ι] (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (hd : q_0 I = h+1)
    (Q : ι → Ideal (MvPolynomial (Fin n) K))
    (hQ : ∀ i, Q i ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hQi : Function.Injective Q) :
    ∑ i, q_16 (Q i) ≤ (p.totalDegree : ℚ) * q_16 I := by
  classical
  let J := I ⊔ Ideal.span {p}
  have hdim : ∀ i, q_0 (Q i) = h := by
    intro i
    let := (hQ i).isPrime
    exact q_119 I (Q i) p hp (hQ i) hd
  have hj := q_84 I p hp (q_8 I) (q_8 J)
    ((q_3 I).mono (fun _ ht => ht.symm))
    ((q_3 J).mono (fun _ ht => ht.symm)) h hd.le
  have hc := q_248 J Q hQ hQi (q_8 J)
    (fun i => q_8 (Q i)) (q_3 J)
    (fun i => q_3 (Q i)) hj.1 (fun i => (hdim i).le)
  have hf : (0 : ℚ) ≤ (h.factorial : ℚ) := Nat.cast_nonneg _
  calc
    ∑ i, q_16 (Q i) = (h.factorial : ℚ) * ∑ i, (q_8 (Q i)).coeff h := by
      simp only [q_16, hdim, Finset.mul_sum]
    _ ≤ (h.factorial : ℚ) * (q_8 J).coeff h := mul_le_mul_of_nonneg_left hc hf
    _ ≤ (h.factorial : ℚ) * ((p.totalDegree : ℚ) * (h+1) * (q_8 I).coeff (h+1)) :=
      mul_le_mul_of_nonneg_left hj.2 hf
    _ = (p.totalDegree : ℚ) * q_16 I := by
      rw [q_16, hd, Nat.factorial_succ]
      push_cast
      ring
end
open MvPolynomial
def q_76 {σ ι K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ) (D : ℕ) : Prop :=
  ∀ p : MvPolynomial σ K, p.totalDegree ≤ D →
    ((∀ i, eval (fun l => (z i l : K)) p = 0) ↔ p ∈ I)
theorem q_366 {σ ι K : Type*}
    [Fintype σ] [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ)
    (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (D : ℕ) (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    (∃ G : MvPolynomial σ ℤ,
      G.totalDegree ≤ D ∧
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤
        q_11 ((D + Fintype.card σ).choose (Fintype.card σ)) (H^D)) ∧
      (∀ i, eval (z i) G = 0) ∧ MvPolynomial.map (Int.castRingHom K) G ∉ I) ∨
    q_76 I z D := by
  classical
  obtain ⟨G,hdeg,hheight,hvan,hspan⟩ :=
    q_73 (F := K) z H hH hz D
  by_cases hGI : ∀ a, MvPolynomial.map (Int.castRingHom K) (G a) ∈ I
  · right
    intro p hp
    constructor
    · intro hvanp
      exact (Submodule.span_le.mpr (by rintro _ ⟨a,rfl⟩; exact hGI a) :
        Submodule.span K (Set.range (fun a => MvPolynomial.map (Int.castRingHom K) (G a))) ≤
          I.restrictScalars K) (hspan p hp hvanp)
    · exact hzI p
  · left
    obtain ⟨a,ha⟩ := not_forall.mp hGI
    exact ⟨G a,hdeg a,hheight a,hvan a,ha⟩
end QuarticPowerFree
end OAI
end
section
namespace OAI
universe u
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators
theorem q_451 {ι σ K : Type*} [Fintype ι] [Field K]
    (z : ι → σ → K) (hz : Function.Injective z) (v : ι → K) :
    ∃ p : MvPolynomial σ K, ∀ i, eval (z i) p = v i := by
  classical
  have hsep : ∀ i j : ι, i ≠ j → ∃ a, z i a ≠ z j a := by
    intro i j hij
    by_contra! h
    exact hij (hz (funext h))
  let L : ι → ι → MvPolynomial σ K := fun i j =>
    if hij : i = j then 1 else
      let a := (hsep i j hij).choose
      C ((z i a - z j a)⁻¹) * (X a - C (z j a))
  have hLi : ∀ i j, eval (z i) (L i j) = 1 := by
    intro i j
    by_cases h : i = j
    · simp [L, h]
    · simp only [L, h, ↓reduceDIte, map_mul, eval_C, map_sub, eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep i j h).choose_spec)
  have hLj : ∀ i j, i ≠ j → eval (z j) (L i j) = 0 := by
    intro i j h
    simp [L, h]
  refine ⟨∑ i, C (v i) * ∏ j, L i j, ?_⟩
  intro a
  rw [map_sum, Finset.sum_eq_single a]
  · simp [hLi]
  · intro i _ hia
    rw [map_mul, eval_C, map_prod]
    have hp : (∏ j, eval (z a) (L i j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (hLj i a hia)
    rw [hp, mul_zero]
  · simp
end
section
open MvPolynomial
open scoped Classical
theorem q_143 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) :
    ∃ j : Fin (q_0 I) → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) := by
  obtain ⟨P,j,hj,hi,_,N,hN⟩ := q_59 I hI
  have he : P = q_8 I := by
    apply q_56
    filter_upwards [Filter.eventually_atTop.mpr ⟨N,hN⟩,q_3 I] with T hp hq
    exact hp.symm.trans hq
  subst P
  exact ⟨j,hj,hi⟩
theorem q_389 {n D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hD : q_16 I ≤ D) (z : ι → Fin n → ℤ)
    (hdet : q_76 I z D)
    (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    ∃ J : Set (Fin n), Nat.card J = q_0 I ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) ℤ,
        (∀ i, (G i).totalDegree ≤ D) ∧
        (∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ q_11 ((D+n).choose n) (H^D)) ∧
        (∀ i, MvPolynomial.map (Int.castRingHom K) (G i) ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (MvPolynomial.map (Int.castRingHom K) (G i))) ∉ I := by
  obtain ⟨j,_,hj⟩ := q_143 I (Ideal.IsPrime.ne_top inferInstance)
  obtain hc | hp := q_463 I (q_8 I) le_rfl
    (q_3 I) hD j hj z hzI H hH hz
  · obtain ⟨G,hG,_,hvan,hnot⟩ := hc
    have hd : (MvPolynomial.map (Int.castRingHom K) G).totalDegree ≤ D := by
      simpa only [totalDegree, support_map_of_injective G (f := Int.castRingHom K) (Int.cast_injective (α := K))] using hG
    have hv : ∀ i, eval (fun l => (z i l : K)) (MvPolynomial.map (Int.castRingHom K) G) = 0 := by
      intro i
      have he := map_eval (Int.castRingHom K) (z i) G
      rw [hvan i, map_zero] at he
      exact he.symm
    exact (hnot ((hdet _ hd).mp hv)).elim
  · exact hp
theorem q_324 {n : ℕ} {K : Type*} [Field K]
    (J : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → K)
    (hz : ∀ p ∈ J, eval z p = 0) :
    ∃ Q ∈ J.minimalPrimes, ∀ p ∈ Q, eval z p = 0 := by
  let P := RingHom.ker (eval z)
  have hP : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le (show J ≤ P from hz)
  exact ⟨Q,hQ,fun p hp => hQP hp⟩
end
open MvPolynomial
theorem q_491 {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : q_0 I = 0) : I.IsMaximal := by
  have ht := q_45 I (q_8 I) (q_3 I)
  change (q_0 I : Cardinal) = _ at ht
  rw [hd, Nat.cast_zero] at ht
  let : Algebra.IsAlgebraic K (MvPolynomial (Fin n) K ⧸ I) := trdeg_eq_zero_iff.mp ht.symm
  exact Ideal.Quotient.maximal_of_isField I (isField_of_isIntegral_of_isField' (R := K)
    (S := MvPolynomial (Fin n) K ⧸ I) (Field.toIsField K))
theorem q_130 {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : q_0 I = 0) (z : Fin n → K)
    (hz : ∀ p ∈ I, eval z p = 0) : I = RingHom.ker (eval z) := by
  apply (q_491 I hd).eq_of_le (RingHom.ker_isPrime _).ne_top
  exact hz
theorem q_477 {n D : ℕ} {ι K : Type*} [Nonempty ι] [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : q_0 I = 0) (z : ι → Fin n → ℤ)
    (hz : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0) : q_76 I z D := by
  intro p _
  constructor
  · intro hp
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [q_130 I hd (fun l => (z i l : K)) (fun q hq => hz q hq i)]
    exact hp i
  · exact hz p
open MvPolynomial
open scoped BigOperators
open scoped Classical
structure q_1 (n : ℕ) where
  free : Set (Fin n)
  equations : ↥(freeᶜ) → MvPolynomial (Fin n) ℤ
noncomputable def q_1.minor {n : ℕ} (P : q_1 n) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (fun i j : ↥(P.freeᶜ) => pderiv j.val (P.equations i))
def q_1.On {n : ℕ} {K : Type*} [Field K]
    (P : q_1 n) (I : Ideal (MvPolynomial (Fin n) K)) : Prop :=
  Nat.card P.free = q_0 I ∧
  (∀ i, MvPolynomial.map (Int.castRingHom K) (P.equations i) ∈ I) ∧
  MvPolynomial.map (Int.castRingHom K) P.minor ∉ I
def q_1.Bounded {n : ℕ} (P : q_1 n) (D : ℕ) (H : ℝ) : Prop :=
  ∃ d ≤ D, (∀ i, (P.equations i).totalDegree ≤ d) ∧
    ∀ i m, |(((P.equations i).coeff m : ℤ) : ℝ)| ≤
      q_11 ((d+n).choose n) (H^d)
def q_64 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) : Prop :=
  ∀ p ∈ I, eval (fun l => (z l : K)) p = 0
theorem q_1.Bounded.mono {n D E : ℕ} {P : q_1 n} {H : ℝ}
    (h : P.Bounded D H) (hDE : D ≤ E) : P.Bounded E H := by
  obtain ⟨d,hd,hdeg,hheight⟩ := h
  exact ⟨d,hd.trans hDE,hdeg,hheight⟩
theorem q_396 {n : ℕ} {K : Type*} [Field K] (P : q_1 n) :
    MvPolynomial.map (Int.castRingHom K) P.minor =
      Matrix.det (fun i j : ↥(P.freeᶜ) => pderiv j.val
        (MvPolynomial.map (Int.castRingHom K) (P.equations i))) := by
  let M : Matrix ↥(P.freeᶜ) ↥(P.freeᶜ) (MvPolynomial (Fin n) ℤ) :=
    fun i j => pderiv j.val (P.equations i)
  have he := (MvPolynomial.map (Int.castRingHom K)).map_det M
  calc
    MvPolynomial.map (Int.castRingHom K) P.minor =
      Matrix.det (fun i j => MvPolynomial.map (Int.castRingHom K) (M i j)) := he
    _ = _ := by congr 1; funext i j; exact pderiv_map.symm
theorem q_194 {n D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hD : q_16 I ≤ D) (z : ι → Fin n → ℤ)
    (hdet : q_76 I z D)
    (hzI : ∀ i, q_64 I (z i))
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    ∃ P : q_1 n, P.On I ∧ P.Bounded D H := by
  obtain ⟨J,hJ,G,hdeg,hheight,hGI,hminor⟩ := q_389 I hD z hdet
    (fun p hp i => hzI i p hp) H hH hz
  let P : q_1 n := ⟨J,G⟩
  refine ⟨P,⟨hJ,hGI,?_⟩,D,le_rfl,hdeg,hheight⟩
  simpa only [q_396] using hminor
theorem q_1.minor_degree_le {n D : ℕ} {P : q_1 n} {H : ℝ}
    (h : P.Bounded D H) : P.minor.totalDegree ≤ n * D := by
  obtain ⟨d,hd,hdeg,_⟩ := h
  apply (q_447 P.equations Subtype.val d hdeg).trans
  apply Nat.mul_le_mul
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ∈ P.freeᶜ)
  · exact (Nat.sub_le _ _).trans hd
theorem q_231 {n h e D : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (he : q_16 I ≤ e) (p : MvPolynomial (Fin n) K)
    (hp : p ∉ I) (hpD : p.totalDegree ≤ D) (hd : q_0 I = h+1) :
    ∃ Q : Finset (Ideal (MvPolynomial (Fin n) K)),
      Q.card ≤ D*e ∧
      (∀ J ∈ Q, J.IsPrime ∧ I ≤ J ∧ q_0 J = h ∧ q_16 J ≤ D*e) ∧
      (∀ z : Fin n → K, (∀ F ∈ I, eval z F = 0) → eval z p = 0 →
        ∃ J ∈ Q, ∀ F ∈ J, eval z F = 0) := by
  classical
  let J := I ⊔ Ideal.span {p}
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) J).toFinset
  have hQ : ∀ q : Q, q.val ∈ J.minimalPrimes := fun q =>
    (Set.Finite.mem_toFinset _).mp q.property
  have hsum : ∑ q ∈ Q, q_16 q ≤ (D*e : ℕ) := by
    calc
      ∑ q ∈ Q, q_16 q ≤ (p.totalDegree : ℚ) * q_16 I := by
        simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
          q_239 I p hp hd (fun q : Q => q.val) hQ Subtype.val_injective
      _ ≤ (D : ℚ) * e := mul_le_mul (by exact_mod_cast hpD) he
        ((q_185 I Ideal.IsPrime.ne_top').trans' zero_le_one) (Nat.cast_nonneg _)
      _ = (D*e : ℕ) := by norm_cast
  have hnonneg : ∀ q ∈ Q, (0 : ℚ) ≤ q_16 q := fun q hq =>
    zero_le_one.trans (q_185 q (hQ ⟨q,hq⟩).isPrime.ne_top)
  refine ⟨Q,?_,?_,?_⟩
  · have hc : (Q.card : ℚ) ≤ ∑ q ∈ Q, q_16 q := by
      calc
        (Q.card : ℚ) = ∑ _q ∈ Q, (1 : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun q hq => q_185 q (hQ ⟨q,hq⟩).isPrime.ne_top
    exact_mod_cast hc.trans hsum
  · intro q hq
    have hm := hQ ⟨q,hq⟩
    let := hm.isPrime
    refine ⟨hm.isPrime,?_,q_119 I q p hp hm hd,?_⟩
    · exact le_sup_left.trans hm.1.2
    · simpa only [Nat.cast_mul] using (Finset.single_le_sum hnonneg hq).trans hsum
  · intro z hz hpz
    obtain ⟨q,hq,hzq⟩ := q_324 J z (show J ≤ RingHom.ker (eval z) from
      sup_le hz (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpz)))
    exact ⟨q,(Set.Finite.mem_toFinset _).mpr hq,hzq⟩
end QuarticPowerFree
end OAI
end
section
namespace OAI
universe u
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped Classical
theorem q_309 {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial (Fin n) ℤ) :
    (MvPolynomial.map (Int.castRingHom K) p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective p (f := Int.castRingHom K)
    (Int.cast_injective (α := K))]
theorem q_218 {n : ℕ} {K : Type*} [Field K]
    (p : MvPolynomial (Fin n) ℤ) (z : Fin n → ℤ) :
    eval (fun l => (z l : K)) (MvPolynomial.map (Int.castRingHom K) p) = (eval z p : K) :=
  (map_eval (Int.castRingHom K) z p).symm
theorem q_485 {n D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (hD : q_16 I ≤ D)
    (S : Finset (Fin n → ℤ)) (hSI : ∀ z ∈ S, q_64 I z)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ p : MvPolynomial (Fin n) K, p ∉ I ∧ p.totalDegree ≤ (n+1)*D ∧
      ∃ L : List (q_1 n), L.length ≤ 1 ∧
        (∀ P ∈ L, P.On I ∧ P.Bounded D H ∧
          q_76 I (fun z : S => z.val) D) ∧
        ∀ z ∈ S, eval (fun l => (z l : K)) p = 0 ∨
          ∃ P ∈ L, eval z P.minor ≠ 0 := by
  obtain hc | hd := q_366 I (fun z : S => z.val)
    (fun p hp z => hSI z.val z.property p hp) D H hH (fun z => hz z.val z.property)
  · obtain ⟨G,hG,_,hvan,hnot⟩ := hc
    refine ⟨MvPolynomial.map (Int.castRingHom K) G,hnot,?_,[],by simp,by simp,?_⟩
    · rw [q_309]
      exact hG.trans (Nat.le_mul_of_pos_left D (Nat.succ_pos n))
    · intro z hzs
      left
      rw [q_218, hvan ⟨z,hzs⟩, Int.cast_zero]
  · obtain ⟨P,hPI,hP⟩ := q_194 I hD (fun z : S => z.val) hd
      (fun z => hSI z.val z.property) H hH (fun z => hz z.val z.property)
    refine ⟨MvPolynomial.map (Int.castRingHom K) P.minor,hPI.2.2,?_,[P],by simp,?_,?_⟩
    · rw [q_309]
      exact (P.minor_degree_le hP).trans (Nat.mul_le_mul_right D (Nat.le_succ n))
    · simpa using And.intro hPI (And.intro hP hd)
    · intro z _
      by_cases h : eval z P.minor = 0
      · left
        rw [q_218,h,Int.cast_zero]
      · exact Or.inr ⟨P,by simp,h⟩
end
section
open MvPolynomial
open scoped Classical
def q_103 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ)) (D : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin n) K, p.totalDegree ≤ D →
    ((∀ z ∈ S, q_64 I z → eval (fun l => (z l : K)) p = 0) ↔ p ∈ I)
theorem q_64.mono {n : ℕ} {K : Type*} [Field K]
    {I J : Ideal (MvPolynomial (Fin n) K)} (hIJ : I ≤ J) {z : Fin n → ℤ}
    (hz : q_64 J z) : q_64 I z := fun p hp => hz p (hIJ hp)
theorem q_162 {n D E : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ))
    (hS : ∀ z ∈ S, q_64 I z) (h : q_76 I (fun z : S => z.val) D)
    (hED : E ≤ D) : q_103 I S E := by
  intro p hp
  rw [← h p (hp.trans hED)]
  constructor
  · intro he z
    exact he z.val z.property (hS z.val z.property)
  · intro he z hz _
    exact he ⟨z,hz⟩
theorem q_103.of_filter {n D : ℕ} {K : Type*} [Field K]
    {I J : Ideal (MvPolynomial (Fin n) K)} (hIJ : I ≤ J)
    (S : Finset (Fin n → ℤ)) (h : q_103 J (S.filter (q_64 I)) D) :
    q_103 J S D := by
  intro p hp
  rw [← h p hp]
  constructor
  · intro he z hz hj
    exact he z (Finset.mem_filter.mp hz).1 hj
  · intro he z hz hj
    exact he z (Finset.mem_filter.mpr ⟨hz,hj.mono hIJ⟩) hj
def q_155 (n D e : ℕ) : ℕ := ((n+1)*max e D)*e
def q_36 (n D : ℕ) : ℕ → ℕ → ℕ
  | 0,e => max e D
  | h+1,e => max (max e D) (q_36 n D h (q_155 n D e))
def q_19 (n D : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 1
  | h+1,e => 1+q_155 n D e * q_19 n D h (q_155 n D e)
theorem q_290 (n D h e : ℕ) : max e D ≤ q_36 n D h e := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact Nat.le_max_left _ _
theorem q_408 (n D h e : ℕ) : 1 ≤ q_19 n D h e := by
  cases h <;> simp only [q_19] <;> omega
def q_198 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ))
    (D h B : ℕ) (H : ℝ) (C : Ideal (MvPolynomial (Fin n) K) × q_1 n) : Prop :=
  C.1.IsPrime ∧ I ≤ C.1 ∧ q_0 C.1 ≤ h ∧ q_16 C.1 ≤ B ∧
    C.2.On C.1 ∧ C.2.Bounded B H ∧ q_103 C.1 S D
def q_43 {n : ℕ} {K : Type*} [Field K]
    (C : Ideal (MvPolynomial (Fin n) K) × q_1 n) (z : Fin n → ℤ) : Prop :=
  q_64 C.1 z ∧ eval z C.2.minor ≠ 0
theorem q_307 {n D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (hd : q_0 I = 0)
    (hD : q_16 I ≤ D) (S : Finset (Fin n → ℤ)) (hS : S.Nonempty)
    (hSI : ∀ z ∈ S, q_64 I z) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ P : q_1 n, P.On I ∧ P.Bounded D H ∧
      q_103 I S D ∧ ∀ z ∈ S, q_43 (I,P) z := by
  let : Nonempty S := hS.to_subtype
  have hdet : q_76 I (fun z : S => z.val) D :=
    q_477 I hd _ (fun p hp z => hSI z.val z.property p hp)
  obtain ⟨P,hPI,hP⟩ := q_194 I hD (fun z : S => z.val) hdet
    (fun z => hSI z.val z.property) H hH (fun z => hz z.val z.property)
  refine ⟨P,hPI,hP,q_162 I S hSI hdet le_rfl,?_⟩
  intro z hzs
  refine ⟨hSI z hzs,?_⟩
  intro hzero
  apply hPI.2.2
  rw [q_130 I hd (fun l => (z l : K)) (hSI z hzs)]
  change eval (fun l => (z l : K)) (MvPolynomial.map (Int.castRingHom K) P.minor) = 0
  rw [q_218,hzero,Int.cast_zero]
theorem q_136 {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length*B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
theorem q_146 {n : ℕ} {K : Type u} [Field K] [CharZero K]
    (D h e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : q_0 I ≤ h) (he : q_16 I ≤ e)
    (S : Finset (Fin n → ℤ)) (hSI : ∀ z ∈ S, q_64 I z)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × q_1 n),
      L.length ≤ q_19 n D h e ∧
      (∀ C ∈ L, q_198 I S D h (q_36 n D h e) H C) ∧
      ∀ z ∈ S, ∃ C ∈ L, q_43 C z := by
  classical
  induction h generalizing e I S with
  | zero =>
    by_cases hS : S.Nonempty
    · have hd : q_0 I = 0 := Nat.eq_zero_of_le_zero hdim
      obtain ⟨P,hPI,hP,hl,hcov⟩ := q_307 I hd
        (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hS hSI H hH hz
      refine ⟨[(I,P)],by simp [q_19],?_,?_⟩
      · intro C hC
        have hC : C = (I,P) := by simpa using hC
        subst C
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP,?_⟩
        · exact he.trans (by exact_mod_cast Nat.le_max_left e D)
        · intro p hp
          exact hl p (hp.trans (Nat.le_max_right _ _))
      · intro z hzs
        exact ⟨(I,P),by simp,hcov z hzs⟩
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hzs
      exact (hS ⟨z,hzs⟩).elim
  | succ h ih =>
    by_cases hS : S.Nonempty
    swap
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hzs
      exact (hS ⟨z,hzs⟩).elim
    by_cases hd : q_0 I = 0
    · obtain ⟨P,hPI,hP,hl,hcov⟩ := q_307 I hd
        (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hS hSI H hH hz
      have hB := q_290 n D (h+1) e
      refine ⟨[(I,P)],?_,?_,?_⟩
      · simpa using q_408 n D (h+1) e
      · intro C hC
        have hC : C = (I,P) := by simpa using hC
        subst C
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP.mono hB,?_⟩
        · exact he.trans (by exact_mod_cast (Nat.le_max_left e D).trans hB)
        · intro p hp
          exact hl p (hp.trans (Nat.le_max_right _ _))
      · intro z hzs
        exact ⟨(I,P),by simp,hcov z hzs⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hkh : k ≤ h := by omega
    obtain ⟨p,hp,hpD,L₀,hL₀,hgood₀,hcover₀⟩ := q_485 I
      (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hSI H hH hz
    let E := q_155 n D e
    obtain ⟨Q,hcard,hQ,hcoverQ⟩ := q_231 I he p hp hpD hk
    let S' := fun q : Q => S.filter (q_64 q.val)
    have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × q_1 n),
        L.length ≤ q_19 n D h E ∧
        (∀ C ∈ L, q_198 q.val (S' q) D h (q_36 n D h E) H C) ∧
        ∀ z ∈ S' q, ∃ C ∈ L, q_43 C z := by
      intro q
      have hq := hQ q.val q.property
      let := hq.1
      apply ih E q.val (hq.2.2.1.le.trans hkh)
        (by simpa only [E,q_155,Nat.cast_mul] using hq.2.2.2) (S' q)
      · intro z hzs
        exact (Finset.mem_filter.mp hzs).2
      · intro z hzs
        exact hz z (Finset.mem_filter.mp hzs).1
    choose L hlen hgood hcover using hc
    let R := Q.attach.toList.flatMap L
    have hRlen : R.length ≤ Q.card * q_19 n D h E := by
      simpa [R] using q_136 Q.attach.toList L (q_19 n D h E)
        (fun q _ => hlen q)
    refine ⟨L₀.map (fun P => (I,P)) ++ R,?_,?_,?_⟩
    · simp only [List.length_append,List.length_map]
      exact (Nat.add_le_add hL₀ hRlen).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcard) 1)
    · intro C hC
      rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨P,hPL,rfl⟩ := List.mem_map.mp hC
        obtain ⟨hPI,hP,hdet⟩ := hgood₀ P hPL
        have hB := q_290 n D (h+1) e
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP.mono hB,?_⟩
        · exact he.trans (by exact_mod_cast (Nat.le_max_left e D).trans hB)
        · exact q_162 I S hSI hdet (Nat.le_max_right _ _)
      · obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
        obtain ⟨hpq,hIq,hdq,heq,hOn,hBound,hLock⟩ := hgood q C hCL
        have hB : q_36 n D h E ≤ q_36 n D (h+1) e := Nat.le_max_right _ _
        refine ⟨hpq,(hQ q.val q.property).2.1.trans hIq,hdq.trans (Nat.le_succ _),?_,
          hOn,hBound.mono hB,?_⟩
        · exact heq.trans (by exact_mod_cast hB)
        · exact hLock.of_filter hIq S
    · intro z hzs
      rcases hcover₀ z hzs with hpz | ⟨P,hPL,hPz⟩
      · obtain ⟨q,hq,hzq⟩ := hcoverQ (fun l => (z l : K)) (hSI z hzs) hpz
        obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hzs,hzq⟩)
        refine ⟨C,List.mem_append_right _ ?_,hCz⟩
        exact List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hCL⟩
      · exact ⟨(I,P),List.mem_append_left _ (List.mem_map.mpr ⟨P,hPL,rfl⟩),hSI z hzs,hPz⟩
end
open MvPolynomial
open scoped Classical
def q_341 {n : ℕ} (S : Finset (Fin n → ℤ)) (D : ℕ) :
    Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) D) where
  carrier := {p | ∀ z ∈ S, eval (fun l => (z l : ℂ)) p.val = 0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq z hz; simpa using congrArg₂ (· + ·) (hp z hz) (hq z hz)
  smul_mem' := by intro a p hp z hz; simp [hp z hz]
noncomputable def q_98 {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z : Fin n → ℤ) (Q : Finset ℕ) : Finset (Fin n → ℤ) :=
  S.filter fun w => q_64 I w ∧ ∀ p ∈ Q, ∀ l, (p : ℤ) ∣ w l-z l
theorem q_386 {n D : ℕ} {S T : Finset (Fin n → ℤ)}
    (hST : S ⊆ T) : q_341 T D ≤ q_341 S D := by
  intro p hp z hz
  exact hp z (hST hz)
theorem q_414 {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z : Fin n → ℤ) {Q R : Finset ℕ} (hQR : Q ⊆ R) :
    q_98 S I z R ⊆ q_98 S I z Q := by
  intro w hw
  obtain ⟨hw,hI,hres⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw,hI,fun p hp l => hres p (hQR hp) l⟩
theorem q_244 {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z w : Fin n → ℤ) (Q : Finset ℕ)
    (hzw : ∀ p ∈ Q, ∀ l, (p : ℤ) ∣ w l-z l) :
    q_98 S I z Q = q_98 S I w Q := by
  ext x
  simp only [q_98,Finset.mem_filter]
  suffices (∀ p ∈ Q, ∀ l, (p : ℤ) ∣ x l-z l) ↔
      (∀ p ∈ Q, ∀ l, (p : ℤ) ∣ x l-w l) by tauto
  constructor
  · intro h p hp l
    have he : x l-w l = (x l-z l)-(w l-z l) := by ring
    rw [he]
    exact dvd_sub (h p hp l) (hzw p hp l)
  · intro h p hp l
    have he : x l-z l = (x l-w l)+(w l-z l) := by ring
    rw [he]
    exact dvd_add (h p hp l) (hzw p hp l)
end QuarticPowerFree
end OAI
end
section
namespace OAI
universe u
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
open MvPolynomial
def q_12 (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | h+1, e => max e (q_12 D h (D*e))
def q_27 (D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h+1, e => 1+(D*e)*q_27 D h (D*e)
theorem q_446 (D h e : ℕ) : e ≤ q_12 D h e := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact Nat.le_max_left _ _
theorem q_374 (D h e : ℕ) : 1 ≤ q_27 D h e := by
  cases h <;> simp only [q_27] <;> omega
theorem q_365 {n D : ℕ} {K : Type u} [Field K]
    (F : Set (MvPolynomial (Fin n) K))
    (hF : ∀ p ∈ F, p.totalDegree ≤ D) (h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : q_0 I ≤ h) (he : q_16 I ≤ e) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K)),
      L.length ≤ q_27 D h e ∧
      (∀ J ∈ L, J.IsPrime ∧ I ≤ J ∧ q_0 J ≤ q_0 I ∧
        q_16 J ≤ q_12 D h e ∧ F ⊆ J ∧
        (¬ F ⊆ I → q_0 J < q_0 I)) ∧
      (∀ z : Fin n → K, (∀ p ∈ I, eval z p = 0) →
        (∀ p ∈ F, eval z p = 0) → ∃ J ∈ L, ∀ p ∈ J, eval z p = 0) := by
  classical
  induction h generalizing e I with
  | zero =>
    by_cases hFI : F ⊆ I
    · refine ⟨[I],le_rfl,?_,?_⟩
      · intro J hJ
        have hj : J = I := by simpa using hJ
        subst J
        exact ⟨inferInstance,le_rfl,le_rfl,he,hFI,fun hn => (hn hFI).elim⟩
      · intro z hz _
        exact ⟨I,by simp,hz⟩
    · refine ⟨[],by simp [q_27],by simp,?_⟩
      intro z hz hFz
      exfalso
      apply hFI
      rw [q_130 I (Nat.eq_zero_of_le_zero hd) z hz]
      exact hFz
  | succ h ih =>
    by_cases hFI : F ⊆ I
    · refine ⟨[I],q_374 D (h+1) e,?_,?_⟩
      · intro J hJ
        have hj : J = I := by simpa using hJ
        subst J
        refine ⟨inferInstance,le_rfl,le_rfl,?_,hFI,fun hn => (hn hFI).elim⟩
        exact he.trans (by exact_mod_cast q_446 D (h+1) e)
      · intro z hz _
        exact ⟨I,by simp,hz⟩
    by_cases hd0 : q_0 I = 0
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hz hFz
      exfalso
      apply hFI
      rw [q_130 I hd0 z hz]
      exact hFz
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hkh : k ≤ h := by omega
    obtain ⟨p,hpF,hpI⟩ : ∃ p ∈ F, p ∉ I := by
      exact Set.not_subset.mp hFI
    obtain ⟨Q,hQcard,hQ,hQcov⟩ := q_231 I he p hpI (hF p hpF) hk
    have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K)),
        L.length ≤ q_27 D h (D*e) ∧
        (∀ J ∈ L, J.IsPrime ∧ q.val ≤ J ∧ q_0 J ≤ q_0 q.val ∧
          q_16 J ≤ q_12 D h (D*e) ∧ F ⊆ J ∧
          (¬ F ⊆ q.val → q_0 J < q_0 q.val)) ∧
        (∀ z : Fin n → K, (∀ p ∈ q.val, eval z p = 0) →
          (∀ p ∈ F, eval z p = 0) → ∃ J ∈ L, ∀ p ∈ J, eval z p = 0) := by
      intro q
      obtain ⟨hprime,_,hdq,heq⟩ := hQ q.val q.property
      let := hprime
      exact ih (D*e) q.val (hdq.le.trans hkh) (by simpa only [Nat.cast_mul] using heq)
    choose L hlen hgood hcover using hc
    let R := Q.attach.toList.flatMap L
    refine ⟨R,?_,?_,?_⟩
    · have hh : R.length ≤ Q.card * q_27 D h (D*e) := by
        simpa only [R,Finset.length_toList,Finset.card_attach] using
          q_136 Q.attach.toList L (q_27 D h (D*e))
            (fun q _ => hlen q)
      exact (hh.trans (Nat.mul_le_mul_right _ hQcard)).trans
        (Nat.le_add_left _ _)
    · intro J hJ
      obtain ⟨q,_,hJL⟩ := List.mem_flatMap.mp hJ
      obtain ⟨hpJ,hqJ,hdJ,heJ,hFJ,_⟩ := hgood q J hJL
      have hend : q_0 J < q_0 I := by
        have hdq := (hQ q.val q.property).2.2.1
        omega
      refine ⟨hpJ,(hQ q.val q.property).2.1.trans hqJ,hend.le,?_,hFJ,fun _ => hend⟩
      exact heJ.trans (by exact_mod_cast Nat.le_max_right e (q_12 D h (D*e)))
    · intro z hz hFz
      obtain ⟨q,hq,hzq⟩ := hQcov z hz (hFz p hpF)
      obtain ⟨J,hJL,hzJ⟩ := hcover ⟨q,hq⟩ z hzq hFz
      exact ⟨J,List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hJL⟩,hzJ⟩
theorem q_393 {n : ℕ} {K : Type u} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [J.IsPrime]
    (hIJ : I ≤ J) : q_0 J ≤ q_0 I := by
  have ht := trdeg_le_of_surjective (Ideal.Quotient.factorₐ K hIJ)
    (Ideal.Quotient.factor_surjective hIJ)
  rw [← q_45 I (q_8 I) (q_3 I),
    ← q_45 J (q_8 J) (q_3 J)] at ht
  exact_mod_cast ht
theorem q_163 {n D A h e : ℕ} {K : Type u} [Field K] [CharZero K]
    (F : Set (MvPolynomial (Fin n) K)) (hF : ∀ p ∈ F, p.totalDegree ≤ D)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : q_0 I ≤ h) (he : q_16 I ≤ e)
    (S : Finset (Fin n → ℤ)) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × q_1 n),
      L.length ≤ q_27 D h e * q_19 n A h (q_12 D h e) ∧
      (∀ C ∈ L,
        q_198 I S A h (q_36 n A h (q_12 D h e)) H C ∧
        F ⊆ C.1 ∧ q_0 C.1 ≤ q_0 I ∧
        (¬ F ⊆ I → q_0 C.1 < q_0 I)) ∧
      ∀ z ∈ S, q_64 I z → (∀ p ∈ F, eval (fun l => (z l : K)) p = 0) →
        ∃ C ∈ L, q_43 C z := by
  classical
  obtain ⟨Q,hQlen,hQ,hQcov⟩ := q_365 F hF h e I hd he
  let S' := fun q : {q // q ∈ Q} => S.filter (q_64 q.val)
  have hc : ∀ q : {q // q ∈ Q}, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × q_1 n),
      L.length ≤ q_19 n A h (q_12 D h e) ∧
      (∀ C ∈ L, q_198 q.val (S' q) A h
        (q_36 n A h (q_12 D h e)) H C) ∧
      ∀ z ∈ S' q, ∃ C ∈ L, q_43 C z := by
    intro q
    obtain ⟨hprime,_,hdq,heq,_⟩ := hQ q.val q.property
    let := hprime
    apply q_146 A h (q_12 D h e) q.val (hdq.trans hd) heq
      (S' q)
    · intro z hz; exact (Finset.mem_filter.mp hz).2
    · exact hH
    · intro z hzs; exact hz z (Finset.mem_filter.mp hzs).1
  choose L hlen hgood hcover using hc
  let R := Q.attach.flatMap L
  refine ⟨R,?_,?_,?_⟩
  · have hh : R.length ≤ Q.length * q_19 n A h (q_12 D h e) := by
      simpa only [R,List.length_attach] using q_136 Q.attach L
        (q_19 n A h (q_12 D h e)) (fun q _ => hlen q)
    exact hh.trans (Nat.mul_le_mul_right _ hQlen)
  · intro C hC
    obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
    obtain ⟨hpq,hIq,hdq,heq,hFq,hstrict⟩ := hQ q.val q.property
    obtain ⟨hpC,hqC,hdC,heC,hOn,hBound,hLock⟩ := hgood q C hCL
    let := hpq
    let := hpC
    have hdim := q_393 q.val C.1 hqC
    refine ⟨⟨hpC,hIq.trans hqC,hdC,heC,hOn,hBound,hLock.of_filter hqC S⟩,
      hFq.trans hqC,hdim.trans hdq,?_⟩
    exact fun hn => hdim.trans_lt (hstrict hn)
  · intro z hz hIz hFz
    obtain ⟨q,hq,hzq⟩ := hQcov (fun l => (z l : K)) hIz hFz
    obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hz,hzq⟩)
    refine ⟨C,List.mem_flatMap.mpr ⟨⟨q,hq⟩,?_,hCL⟩,hCz⟩
    exact List.mem_attach Q ⟨q,hq⟩
noncomputable def q_104 {n : ℕ} (S : Finset (Fin n → ℤ)) (d E : ℕ) :
    Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E) :=
  (q_5 d).comap (q_5 E).subtype ⊓ q_341 S E
def q_26 {n : ℕ} (d E : ℕ)
    (W : Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E)) :
    Set (MvPolynomial (Fin n) ℂ) :=
  {p | ∃ v ∈ W, (v : MvPolynomial (Fin n) ℂ) = p ∧ p.totalDegree ≤ d}
theorem q_118 {n d E : ℕ}
    (W : Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E))
    (p : MvPolynomial (Fin n) ℂ) (hp : p ∈ q_26 d E W) :
    p.totalDegree ≤ d := hp.choose_spec.2.2
theorem q_319 {n d E : ℕ} {S T : Finset (Fin n → ℤ)}
    (hST : S ⊆ T) : q_104 T d E ≤ q_104 S d E :=
  inf_le_inf le_rfl (q_386 hST)
theorem q_304 {n d E : ℕ} (hdE : d ≤ E)
    (S : Finset (Fin n → ℤ)) (p : MvPolynomial (Fin n) ℂ) :
    p ∈ q_26 d E (q_104 S d E) ↔
      p.totalDegree ≤ d ∧ ∀ z ∈ S, eval (fun l => (z l : ℂ)) p = 0 := by
  constructor
  · rintro ⟨v,hv,rfl,hdeg⟩
    exact ⟨hdeg,hv.2⟩
  · rintro ⟨hdeg,hz⟩
    refine ⟨⟨p,mem_totalSpace.mpr (hdeg.trans hdE)⟩,?_,rfl,hdeg⟩
    exact ⟨mem_totalSpace.mpr hdeg,hz⟩
structure KernelGeometry (n : ℕ) where
  points : Finset (Fin n → ℤ)
  height : ℝ
  one_le_height : 1 ≤ height
  bounded : ∀ z ∈ points, ∀ l, |(z l : ℝ)| ≤ height
def q_466 {n : ℕ} (h e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) : Prop :=
  I.IsPrime ∧ q_0 I ≤ h ∧ q_16 I ≤ e
noncomputable def q_86 {n E : ℕ} (G : KernelGeometry n) (d A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (W : Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E)) :
    List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n) := by
  classical
  exact if hi : q_466 h e I then
    letI := hi.1
    (q_163 (A := A) (q_26 d E W)
      (q_118 W) I hi.2.1 hi.2.2 G.points G.height
      G.one_le_height G.bounded).choose
  else []
theorem q_168 {n E : ℕ} (G : KernelGeometry n) (d A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (W : Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E))
    (hi : q_466 h e I) :
    (q_86 G d A h e I W).length ≤
      q_27 d h e * q_19 n A h (q_12 d h e) ∧
    (∀ C ∈ q_86 G d A h e I W,
      q_198 I G.points A h (q_36 n A h (q_12 d h e)) G.height C ∧
      q_26 d E W ⊆ C.1 ∧ q_0 C.1 ≤ q_0 I ∧
      (¬ q_26 d E W ⊆ I → q_0 C.1 < q_0 I)) ∧
    ∀ z ∈ G.points, q_64 I z →
      (∀ p ∈ q_26 d E W, eval (fun l => (z l : ℂ)) p = 0) →
      ∃ C ∈ q_86 G d A h e I W, q_43 C z := by
  classical
  let := hi.1
  simpa only [q_86,dif_pos hi] using
    (q_163 (A := A) (q_26 d E W)
      (q_118 W) I hi.2.1 hi.2.2 G.points G.height
      G.one_le_height G.bounded).choose_spec
noncomputable def q_139 {n : ℕ} (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)) :
    Ideal (MvPolynomial (Fin n) ℂ) × q_1 n := by
  classical
  exact (L.find? (fun C => decide (q_43 C z))).getD s
theorem q_413 {n : ℕ} (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n))
    (hL : ∃ C ∈ L, q_43 C z) :
    q_139 z s L ∈ L ∧ q_43 (q_139 z s L) z := by
  classical
  simp only [q_139]
  cases hh : L.find? (fun C => decide (q_43 C z)) with
  | none =>
    obtain ⟨C,hC,hcov⟩ := hL
    have hc := List.find?_eq_none.mp hh C hC
    simp [hcov] at hc
  | some C =>
    simp only [Option.getD_some]
    have hc : decide (q_43 C z) = true :=
      List.find?_some (p := fun C => decide (q_43 C z)) hh
    exact ⟨List.mem_of_find?_eq_some hh,of_decide_eq_true hc⟩
open MvPolynomial
open scoped BigOperators
open scoped Classical
def q_51 (m : ℕ) : ℝ :=
  (1+(m:ℝ)^2) * m.factorial * (1+(m:ℝ))^m
theorem q_409 (m d : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    q_11 m (H^d) ≤ q_51 m * H^(2*d*(m+1)) := by
  have hpow : 1 ≤ (H^d)^2 := one_le_pow₀ (one_le_pow₀ hH)
  have ha : 1+(m:ℝ)^2*(H^d)^2 ≤ (1+(m:ℝ)^2)*(H^d)^2 := by nlinarith
  have hb : 1+(m:ℝ)*(H^d)^2 ≤ (1+(m:ℝ))*(H^d)^2 := by nlinarith
  unfold q_11
  calc
    (1+(m:ℝ)^2*(H^d)^2) * m.factorial * (1+(m:ℝ)*(H^d)^2)^m ≤
        ((1+(m:ℝ)^2)*(H^d)^2) * m.factorial * (((1+(m:ℝ))*(H^d)^2)^m) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
      · exact pow_le_pow_left₀ (by positivity) hb _
      · positivity
      · positivity
    _ = q_51 m * H^(2*d*(m+1)) := by
      rw [q_51,show 2*d*(m+1) = d*2*(m+1) by ring]
      simp only [pow_mul,mul_pow,pow_succ]
      ring
def q_71 (n d m : ℕ) : ℝ :=
  m.factorial * ((((d+n).choose n : ℝ)*(d:ℝ)*q_51 ((d+n).choose n))^m)
def q_93 (n d m : ℕ) : ℕ :=
  (2*d*((d+n).choose n+1)+d)*m
theorem q_115 (n d m : ℕ) : 0 ≤ q_71 n d m := by
  unfold q_71 q_51
  positivity
theorem q_464 {n d : ℕ} {P : q_1 n}
    (hdeg : ∀ i, (P.equations i).totalDegree ≤ d) (H : ℝ) (hH : 1 ≤ H)
    (hc : ∀ i a, |(((P.equations i).coeff a : ℤ) : ℝ)| ≤
      q_11 ((d+n).choose n) (H^d))
    (z : Fin n → ℤ) (hz : ∀ l, |(z l : ℝ)| ≤ H) :
    |((eval z P.minor : ℤ) : ℝ)| ≤
      q_71 n d (Fintype.card ↥(P.freeᶜ)) *
        H^(q_93 n d (Fintype.card ↥(P.freeᶜ))) := by
  let M := (d+n).choose n
  let m := Fintype.card ↥(P.freeᶜ)
  have hC : 0 ≤ q_11 M (H^d) := by unfold q_11; positivity
  have hb := q_342 P.equations Subtype.val d hdeg
    (q_11 M (H^d)) H hC hH hc z hz
  have hi : (M:ℝ)*((d:ℝ)*q_11 M (H^d))*H^d ≤
      ((M:ℝ)*(d:ℝ)*q_51 M)*H^(2*d*(M+1)+d) := by
    calc
      _ ≤ (M:ℝ)*((d:ℝ)*(q_51 M * H^(2*d*(M+1))))*H^d := by
        gcongr
        exact q_409 M d H hH
      _ = _ := by rw [pow_add]; ring
  calc
    |((eval z P.minor : ℤ) : ℝ)| ≤ (m.factorial:ℝ)*
        ((M:ℝ)*((d:ℝ)*q_11 M (H^d))*H^d)^m := by
      simpa only [q_1.minor, m, M, Fintype.card_fin] using hb
    _ ≤ (m.factorial:ℝ)*(((M:ℝ)*(d:ℝ)*q_51 M)*H^(2*d*(M+1)+d))^m := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ _ hi
      positivity
    _ = _ := by
      simp only [q_71,q_93,mul_pow,pow_mul,M,m]
      ring
theorem q_315 (n D : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B : ℕ, ∀ (P : q_1 n) (H : ℝ),
      1 ≤ H → P.Bounded D H → ∀ z : Fin n → ℤ,
        (∀ l, |(z l : ℝ)| ≤ H) → |((eval z P.minor : ℤ) : ℝ)| ≤ C*H^B := by
  classical
  let C : ℝ := 1 + ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1), q_71 n d m
  let B : ℕ := ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1), q_93 n d m
  have hnonneg : ∀ d, 0 ≤ ∑ m ∈ Finset.range (n+1), q_71 n d m := fun d =>
    Finset.sum_nonneg (fun m _ => q_115 n d m)
  have hsum : 0 ≤ ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1),
      q_71 n d m := Finset.sum_nonneg (fun d _ => hnonneg d)
  refine ⟨C, by dsimp [C]; linarith, B, ?_⟩
  intro P H hH hP z hz
  obtain ⟨d,hd,hdeg,hcoeff⟩ := hP
  let m := Fintype.card ↥(P.freeᶜ)
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ∈ P.freeᶜ)
  have hdmem : d ∈ Finset.range (D+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hmmem : m ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hCs : q_71 n d m ≤ C := by
    have h₁ := Finset.single_le_sum (fun j _ => q_115 n d j) hmmem
    have h₂ := Finset.single_le_sum (fun j _ => hnonneg j) hdmem
    dsimp [C]
    linarith
  have hBs : q_93 n d m ≤ B :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (q_93 n d j)) hmmem).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le
        (∑ x ∈ Finset.range (n+1), q_93 n j x)) hdmem)
  exact (q_464 hdeg H hH hcoeff z hz).trans
    (mul_le_mul hCs (pow_le_pow_right₀ hH hBs) (by positivity) (by
      exact (q_115 n d m).trans hCs))
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree
noncomputable def q_75 {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) : ℕ := Module.finrank K (V ⧸ W)
theorem q_495 {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {W W' : Submodule K V} (h : W ≤ W') :
    q_75 W' ≤ q_75 W := by
  simp only [q_75, Submodule.finrank_quotient]
  exact Nat.sub_le_sub_left (Submodule.finrank_mono h) _
theorem q_361 {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {W W' : Submodule K V} (h : W ≤ W') :
    q_75 W = q_75 W' ↔ W = W' := by
  constructor
  · intro he
    apply Submodule.eq_of_le_of_finrank_eq h
    have h₁ := Submodule.finrank_quotient_add_finrank W
    have h₂ := Submodule.finrank_quotient_add_finrank W'
    dsimp [q_75] at he
    omega
  · rintro rfl; rfl
variable {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (W : ℕ → σ → α → Submodule K V)
variable (next : ℕ → σ → Submodule K V → σ)
noncomputable def q_68 : ℕ → ℕ → σ → α → ℕ
  | 0, _, _, _ => 0
  | n+1, i, s, a => q_75 (W i s a) * (Module.finrank K V + 1)^n +
      q_68 n (i+1) (next i s (W i s a)) a
noncomputable def q_17 : ℕ → ℕ → σ → α → List σ
  | 0, _, s, _ => [s]
  | n+1, i, s, a => s :: q_17 n (i+1) (next i s (W i s a)) a
variable [Module.Finite K V]
theorem q_455 (n i : ℕ) (s : σ) (a : α) :
    q_68 W next n i s a < (Module.finrank K V + 1)^n := by
  induction n generalizing i s with
  | zero => simp [q_68]
  | succ n ih =>
    have hr : q_75 (W i s a) ≤ Module.finrank K V := by
      rw [q_75, Submodule.finrank_quotient]
      exact Nat.sub_le _ _
    have ht := ih (i+1) (next i s (W i s a))
    simp only [q_68, pow_succ]
    nlinarith
theorem q_197 (a b : α)
    (hW : ∀ i s, W i s a ≤ W i s b) (n i : ℕ) (s : σ) :
    q_68 W next n i s b ≤ q_68 W next n i s a ∧
    (q_68 W next n i s b = q_68 W next n i s a →
      q_17 W next n i s b = q_17 W next n i s a) := by
  induction n generalizing i s with
  | zero => simp [q_68, q_17]
  | succ n ih =>
    have hr := q_495 (hW i s)
    by_cases he : q_75 (W i s a) = q_75 (W i s b)
    · have hw := (q_361 (hW i s)).mp he
      have hh := ih (i+1) (next i s (W i s a))
      simp only [q_68, q_17, ← hw]
      exact ⟨Nat.add_le_add_left hh.1 _, fun h => congrArg (List.cons s) (hh.2 (Nat.add_left_cancel h))⟩
    · have hl : q_75 (W i s b) + 1 ≤ q_75 (W i s a) := by omega
      have ht := q_455 W next n (i+1) (next i s (W i s b)) b
      have hstrict : q_68 W next (n+1) i s b < q_68 W next (n+1) i s a := by
        simp only [q_68]
        nlinarith
      exact ⟨hstrict.le,fun he => (hstrict.ne he).elim⟩
end QuarticPowerFree
open scoped BigOperators
namespace QuarticPowerFree
theorem q_236 {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (t : ℕ) (f : Finset α → α → M) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, f (S.erase q) q) =
      ∑ B ∈ P.powersetCard t, ∑ q ∈ P \ B, f B q := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun y _ => ⟨y.1.erase y.2, y.2⟩)
  · intro y hy
    obtain ⟨hS, hq⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hSP, hScard⟩ := Finset.mem_powersetCard.mp hS
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.erase_subset _ _).trans hSP,
        by rw [Finset.card_erase_of_mem hq, hScard]; omega⟩
    · exact Finset.mem_sdiff.mpr ⟨hSP hq, Finset.notMem_erase _ _⟩
  · intro y hy z hz heq
    have hq : y.2 = z.2 := congrArg Sigma.snd heq
    have hS : y.1.erase y.2 = z.1.erase z.2 := congrArg Sigma.fst heq
    have hyq := (Finset.mem_sigma.mp hy).2
    have hzq := (Finset.mem_sigma.mp hz).2
    have : y.1 = z.1 := by
      calc
        y.1 = insert y.2 (y.1.erase y.2) := (Finset.insert_erase hyq).symm
        _ = insert z.2 (z.1.erase z.2) := by rw [hS, hq]
        _ = z.1 := Finset.insert_erase hzq
    exact Sigma.ext this (heq_of_eq hq)
  · intro y hy
    obtain ⟨hB, hq⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hBP, hBcard⟩ := Finset.mem_powersetCard.mp hB
    obtain ⟨hqP, hqB⟩ := Finset.mem_sdiff.mp hq
    refine ⟨⟨insert y.2 y.1, y.2⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hqP hBP,
          by rw [Finset.card_insert_of_notMem hqB, hBcard]⟩
      · exact Finset.mem_insert_self _ _
    · simp only [Finset.erase_insert hqB]
  · intro y _
    rfl
noncomputable def q_151 {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) : ℝ :=
  (∑ S ∈ P.powersetCard t, f S) / (P.powersetCard t).card
theorem q_254 {α : Type*} [DecidableEq α] (P : Finset α) (t : ℕ) :
    ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card =
      ((P.card : ℝ) - t) * (P.powersetCard t).card := by
  have h := q_236 P t (fun _ _ => (1 : ℝ))
  have hleft : (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, (1 : ℝ)) =
      ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card := by
    have heq : ∀ S ∈ P.powersetCard (t + 1), (∑ _q ∈ S, (1 : ℝ)) = (t + 1 : ℕ) := by
      intro S hS
      simp [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hright : (∑ B ∈ P.powersetCard t, ∑ _q ∈ P \ B, (1 : ℝ)) =
      ((P.card : ℝ) - t) * (P.powersetCard t).card := by
    have heq : ∀ B ∈ P.powersetCard t, (∑ _q ∈ P \ B, (1 : ℝ)) = (P.card : ℝ) - t := by
      intro B hB
      obtain ⟨hBP, hBt⟩ := Finset.mem_powersetCard.mp hB
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hBP, hBt]
      exact Nat.cast_sub (hBt ▸ Finset.card_le_card hBP)
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hleft, hright] at h
  exact h
theorem q_470 {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard t, ∑ _q ∈ S, f S) =
      (t : ℝ) * ∑ S ∈ P.powersetCard t, f S := by
  have heq : ∀ S ∈ P.powersetCard t, (∑ _q ∈ S, f S) = (t : ℝ) * f S := by
    intro S hS
    simp only [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl heq, Finset.mul_sum]
theorem q_420 {α : Type*} [DecidableEq α] (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard t, ∑ _q ∈ P \ S, f S) =
      ((P.card : ℝ) - t) * ∑ S ∈ P.powersetCard t, f S := by
  have heq : ∀ S ∈ P.powersetCard t, (∑ _q ∈ P \ S, f S) = ((P.card : ℝ) - t) * f S := by
    intro S hS
    obtain ⟨hSP, hSt⟩ := Finset.mem_powersetCard.mp hS
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hSP, hSt,
      Nat.cast_sub (hSt ▸ Finset.card_le_card hSP)]
  rw [Finset.sum_congr rfl heq, Finset.mul_sum]
theorem q_457 {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (ht : t < P.card) (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, f (S.erase q)) /
        (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) = q_151 P t f := by
  rw [q_236 P t (fun S _ => f S), q_420,
    q_254, q_151]
  exact mul_div_mul_left _ _ (sub_ne_zero.mpr (ne_of_gt (Nat.cast_lt.mpr ht)))
theorem q_479 {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, f S) /
        (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) = q_151 P (t + 1) f := by
  rw [q_470, q_151]
  exact mul_div_mul_left _ _ (by positivity)
noncomputable def q_124 {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (bad : Finset α → Finset α) : ℝ :=
  (∑ S ∈ P.powersetCard t, ∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) /
    ((t : ℝ) * (P.powersetCard t).card)
theorem q_348 {α : Type*} [DecidableEq α]
    (R : Finset α → ℕ) (bad : Finset α → Finset α)
    (S : Finset α) (q : α)
    (hmono : R S ≤ R (S.erase q))
    (hstable : R S = R (S.erase q) → bad S = bad (S.erase q)) :
    (if q ∈ bad S then (1 : ℝ) else 0) ≤
      ((R (S.erase q) : ℝ) - R S) + if q ∈ bad (S.erase q) then 1 else 0 := by
  by_cases heq : R S = R (S.erase q)
  · rw [hstable heq, heq, sub_self, zero_add]
  · have hle : R S + 1 ≤ R (S.erase q) := by omega
    have hle' : (R S : ℝ) + 1 ≤ R (S.erase q) := by exact_mod_cast hle
    split_ifs <;> linarith
theorem q_487 {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (bad : Finset α → Finset α) (D : ℕ)
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S,
      if q ∈ bad (S.erase q) then (1 : ℝ) else 0) ≤
        (P.powersetCard t).card * (D : ℝ) := by
  rw [q_236 P t (fun S q => if q ∈ bad S then (1 : ℝ) else 0)]
  calc
    _ ≤ ∑ S ∈ P.powersetCard t, (D : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      rw [Finset.sum_boole]
      apply Nat.cast_le.mpr
      apply le_trans (Finset.card_le_card ?_) (hbad S (Finset.mem_powersetCard.mp hS).1)
      intro q hq
      obtain ⟨hqP, hqbad⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hqP).1, hqbad⟩
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
theorem q_496 {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (ht : t < P.card)
    (R : Finset α → ℕ) (bad : Finset α → Finset α) (D : ℕ)
    (hmono : ∀ S ⊆ P, ∀ q ∈ S, R S ≤ R (S.erase q))
    (hstable : ∀ S ⊆ P, ∀ q ∈ S, R S = R (S.erase q) → bad S = bad (S.erase q))
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    q_124 P (t + 1) bad ≤
      q_151 P t (fun S => R S) - q_151 P (t + 1) (fun S => R S) +
        (D : ℝ) / ((P.card : ℝ) - t) := by
  have hcard : 0 < (P.powersetCard (t + 1)).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
  have hsmall : 0 < (P.powersetCard t).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
  have hden : 0 < ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card :=
    mul_pos (by positivity) (Nat.cast_pos.mpr hcard)
  have hsum :
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) ≤
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, (R (S.erase q) : ℝ)) -
      (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, (R S : ℝ)) +
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S,
        if q ∈ bad (S.erase q) then (1 : ℝ) else 0) := by
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S hS
    apply Finset.sum_le_sum
    intro q hq
    exact q_348 R bad S q
      (hmono S (Finset.mem_powersetCard.mp hS).1 q hq)
      (hstable S (Finset.mem_powersetCard.mp hS).1 q hq)
  have hsum' := div_le_div_of_nonneg_right hsum hden.le
  rw [add_div, sub_div, q_457 P t ht (fun S => (R S : ℝ)),
    q_479 P t (fun S => (R S : ℝ))] at hsum'
  have hbad' := div_le_div_of_nonneg_right (q_487 P t bad D hbad) hden.le
  have herr : ((P.powersetCard t).card * (D : ℝ)) /
      (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) =
        (D : ℝ) / ((P.card : ℝ) - t) := by
    rw [q_254, mul_comm ((P.card : ℝ) - t)]
    exact mul_div_mul_left _ _ (ne_of_gt (Nat.cast_pos.mpr hsmall))
  rw [herr] at hbad'
  change _ ≤ _ at hsum'
  dsimp only [q_124]
  linarith
theorem q_181 {α : Type*}
    (P : Finset α) (t : ℕ) (ht : t ≤ P.card)
    (R : Finset α → ℕ) (B : ℕ) (hR : ∀ S ⊆ P, R S ≤ B) :
    0 ≤ q_151 P t (fun S => R S) ∧ q_151 P t (fun S => R S) ≤ B := by
  have hcard : 0 < (P.powersetCard t).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr ht)
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun S _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · rw [q_151, div_le_iff₀ (Nat.cast_pos.mpr hcard)]
    calc
      _ ≤ ∑ _S ∈ P.powersetCard t, (B : ℝ) := by
        apply Finset.sum_le_sum
        intro S hS
        exact Nat.cast_le.mpr (hR S (Finset.mem_powersetCard.mp hS).1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
theorem q_429 {α : Type*} [DecidableEq α]
    (P : Finset α) (ell T : ℕ) (hT : 0 < T) (hsize : ell + T < P.card)
    (R : Finset α → ℕ) (bad : Finset α → Finset α) (B D : ℕ)
    (hR : ∀ S ⊆ P, R S ≤ B)
    (hmono : ∀ S ⊆ P, ∀ q ∈ S, R S ≤ R (S.erase q))
    (hstable : ∀ S ⊆ P, ∀ q ∈ S, R S = R (S.erase q) → bad S = bad (S.erase q))
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    (∑ j ∈ Finset.range T, q_124 P (ell + j + 1) bad) / (T : ℝ) ≤
      (B : ℝ) / T + (D : ℝ) / ((P.card : ℝ) - (ell + T)) := by
  let F : ℕ → ℝ := fun j => q_151 P (ell + j) (fun S => R S)
  let err : ℝ := (D : ℝ) / ((P.card : ℝ) - (ell + T))
  have hgap : 0 < (P.card : ℝ) - (ell + T) := by
    apply sub_pos.mpr
    exact_mod_cast hsize
  have hstep (j : ℕ) (hj : j ∈ Finset.range T) :
      q_124 P (ell + j + 1) bad ≤ F j - F (j + 1) + err := by
    have hjt := Finset.mem_range.mp hj
    have ht : ell + j < P.card := by omega
    have h := q_496 P (ell + j) ht R bad D hmono hstable hbad
    have herr : (D : ℝ) / ((P.card : ℝ) - (ell + j)) ≤ err := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hgap
      have : (j : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt hjt)
      linarith
    dsimp [F]
    simp only [Nat.add_assoc, Nat.cast_add] at h ⊢
    exact h.trans (by linarith)
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hupper := (q_181 P ell (by omega) R B hR).2
  have hlower := (q_181 P (ell + T) (by omega) R B hR).1
  have hdiff : F 0 - F T ≤ (B : ℝ) := by
    dsimp [F]
    simpa only [Nat.add_zero] using sub_le_self _ hlower |>.trans hupper
  have hsum' : (∑ j ∈ Finset.range T, q_124 P (ell + j + 1) bad) ≤
      (B : ℝ) + T * err := by linarith
  have hT' : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  calc
    _ ≤ ((B : ℝ) + T * err) / T := div_le_div_of_nonneg_right hsum' hT'.le
    _ = (B : ℝ) / T + err := by rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hT')]
    _ = _ := rfl
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
theorem q_182 (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hd : ∀ p ∈ P, (p : ℤ) ∣ a) :
    (∏ p ∈ P, (p : ℝ)) ≤ |(a : ℝ)| := by
  have hn : a.natAbs ≠ 0 := (Int.natAbs_pos.mpr ha).ne'
  have hs : P ⊆ a.natAbs.primeFactors := by
    intro p h
    exact Nat.mem_primeFactors.mpr ⟨hp p h,
      by simpa using Int.natAbs_dvd_natAbs.mpr (hd p h), hn⟩
  have hh := Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
    ((Finset.prod_dvd_prod_of_subset P a.natAbs.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd a.natAbs))
  have he : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [← he, ← Nat.cast_prod]
  exact_mod_cast hh
theorem q_295 (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, (p : ℤ) ∣ a)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X ^ ζ ≤ (p : ℝ)) (hlarge : |(a : ℝ)| ≤ X ^ B) :
    (P.card : ℝ) ≤ B / ζ := by
  have hx : 0 ≤ X := (zero_lt_one.trans hX).le
  have h : X ^ (ζ * (P.card : ℝ)) ≤ X ^ B := by
    rw [Real.rpow_mul hx, Real.rpow_natCast]
    calc
      (X ^ ζ) ^ P.card = ∏ _p ∈ P, X ^ ζ := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod
        (fun _ _ => (Real.rpow_pos_of_pos (zero_lt_one.trans hX) ζ).le) hsmall
      _ ≤ |(a : ℝ)| := q_182 a ha P hp hd
      _ ≤ X ^ B := hlarge
  rw [le_div_iff₀ hζ]
  simpa [mul_comm] using (Real.rpow_le_rpow_left_iff hX).mp h
theorem q_196 (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, (p : ℤ) ∣ a)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X ^ ζ ≤ (p : ℝ)) (hlarge : |(a : ℝ)| ≤ X ^ B) :
    P.card ≤ ⌊B / ζ⌋₊ :=
  Nat.le_floor (q_295 a ha P hp hd X ζ B hX hζ hsmall hlarge)
open scoped BigOperators
theorem q_453 {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : ℕ → σ → α → Submodule K V) (next : ℕ → σ → Submodule K V → σ)
    (n i : ℕ) (s : σ) (a : α) : (q_17 W next n i s a).length = n+1 := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [q_17, List.length_cons, ih]
theorem q_380 {σ : Type*} (l : List σ) (minor : σ → ℤ)
    (X B : ℝ) (hX : 0 < X)
    (hminor : ∀ s ∈ l, minor s ≠ 0 ∧ |(minor s : ℝ)| ≤ X^B) :
    (l.map minor).prod ≠ 0 ∧ |(((l.map minor).prod : ℤ) : ℝ)| ≤ X^(B*(l.length : ℝ)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hminor x (by simp)
    have ht := ih (fun s hs => hminor s (by simp [hs]))
    constructor
    · simpa only [List.map_cons, List.prod_cons] using mul_ne_zero hx.1 ht.1
    · simp only [List.map_cons, List.prod_cons, Int.cast_mul, abs_mul,
        List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
        Real.rpow_add hX]
      exact (mul_le_mul hx.2 ht.2 (abs_nonneg _) (Real.rpow_nonneg hX.le _)).trans_eq (mul_comm _ _)
theorem q_418 {K V σ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V]
    (W : ℕ → σ → Finset ℕ → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ)
    (hW : ∀ i s A B, A ⊆ B → W i s A ≤ W i s B)
    (minor : σ → ℤ) (n : ℕ) (s : σ)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X^ζ ≤ (p : ℝ))
    (hminor : ∀ A ⊆ P, ∀ t ∈ q_17 W next n 0 s A,
      minor t ≠ 0 ∧ |(minor t : ℝ)| ≤ X^B)
    (ell T : ℕ) (hT : 0 < T) (hsize : ell+T < P.card) :
    let bad := fun A => P.filter fun p : ℕ =>
      (p : ℤ) ∣ ((q_17 W next n 0 s A).map minor).prod
    (∑ j ∈ Finset.range T, q_124 P (ell+j+1) bad) / (T : ℝ) ≤
      (((Module.finrank K V+1)^n : ℕ) : ℝ) / T +
      (⌊(B*(n+1:ℕ))/ζ⌋₊ : ℝ) / ((P.card : ℝ) - (ell+T)) := by
  classical
  intro bad
  let R := fun A => q_68 W next n 0 s A
  apply q_429 P ell T hT hsize R bad
    ((Module.finrank K V+1)^n) ⌊(B*(n+1:ℕ))/ζ⌋₊
  · intro A _
    exact (q_455 W next n 0 s A).le
  · intro A _ q _
    exact (q_197 W next (A.erase q) A
      (fun i s => hW i s _ _ (Finset.erase_subset _ _)) n 0 s).1
  · intro A _ q _ he
    have hs := (q_197 W next (A.erase q) A
      (fun i s => hW i s _ _ (Finset.erase_subset _ _)) n 0 s).2 he
    dsimp [bad]
    rw [hs]
  · intro A hAP
    let l := q_17 W next n 0 s A
    have hb := q_380 l minor X B (zero_lt_one.trans hX) (hminor A hAP)
    have hl : l.length = n+1 := q_453 W next n 0 s A
    have hin : P ∩ bad A = bad A := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hin]
    apply q_196 _ hb.1 _
      (fun p h => hp p (Finset.mem_filter.mp h).1)
      (fun _ h => (Finset.mem_filter.mp h).2) X ζ (B*(n+1:ℕ)) hX hζ
      (fun p h => hsmall p (Finset.mem_filter.mp h).1)
    simpa only [hl] using hb.2
open scoped BigOperators
def q_110 (P : Finset ℕ) (ell T : ℕ) :=
  Σ j : Fin T, (P.powersetCard (ell+j.val+1))
noncomputable instance (P : Finset ℕ) (ell T : ℕ) : Fintype (q_110 P ell T) :=
  inferInstanceAs (Fintype (Σ j : Fin T, (P.powersetCard (ell+j.val+1))))
noncomputable def q_367 (P : Finset ℕ) (ell T : ℕ)
    (a : q_110 P ell T) : ℝ :=
  ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹
def q_391 {P : Finset ℕ} {ell T : ℕ} (a : q_110 P ell T) : Finset ℕ :=
  a.2.val
theorem q_435 {P : Finset ℕ} {ell T : ℕ} (a : q_110 P ell T) :
    q_391 a ⊆ P ∧ (q_391 a).card = ell+a.1.val+1 :=
  Finset.mem_powersetCard.mp a.2.property
theorem q_489 (P : Finset ℕ) (ell T : ℕ)
    (a : q_110 P ell T) : 0 ≤ q_367 P ell T a := by
  unfold q_367
  positivity
theorem q_503 (P : Finset ℕ) (ell T : ℕ)
    (hT : 0 < T) (hsize : ell+T ≤ P.card) :
    ∑ a : q_110 P ell T, q_367 P ell T a = 1 := by
  classical
  change (∑ a : Σ j : Fin T, (P.powersetCard (ell+j.val+1)),
    ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹) = 1
  rw [Fintype.sum_sigma]
  have he (j : Fin T) :
      (∑ _a : (P.powersetCard (ell+j.val+1)),
        ((T : ℝ) * ((P.powersetCard (ell+j.val+1)).card : ℝ))⁻¹) = (T : ℝ)⁻¹ := by
    have hc : 0 < (P.powersetCard (ell+j.val+1)).card :=
      Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hT.ne')
theorem q_415 (P : Finset ℕ) (ell T : ℕ)
    (bad : Finset ℕ → Finset ℕ) :
    (∑ a : q_110 P ell T, q_367 P ell T a *
      ((∑ q ∈ q_391 a, if q ∈ bad (q_391 a) then (1 : ℝ) else 0) /
        (q_391 a).card)) =
      (∑ j ∈ Finset.range T, q_124 P (ell+j+1) bad) / T := by
  classical
  change (∑ a : Σ j : Fin T, (P.powersetCard (ell+j.val+1)),
    ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹ *
      ((∑ q ∈ a.2.val, if q ∈ bad a.2.val then (1 : ℝ) else 0) / a.2.val.card)) = _
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [q_124]
  rw [Finset.sum_coe_sort (P.powersetCard (ell+j.val+1))
    (fun S : Finset ℕ => ((T : ℝ) * ((P.powersetCard (ell+j.val+1)).card : ℝ))⁻¹ *
      ((∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) / S.card)),
    Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_powersetCard.mp ha).2]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring
theorem q_426 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (i : ι)
    (F : (∀ j, Ω j) → ℝ) (C : ℝ)
    (hF : ∀ x, (∑ a, w i a * F (Function.update x i a)) ≤ C) :
    (∑ x, (∏ j, w j (x j)) * F x) ≤ C := by
  classical
  let E := Equiv.piSplitAt i Ω
  let W : (∀ j : {j // j ≠ i}, Ω j) → ℝ := fun x => ∏ j : {j // j ≠ i}, w j.val (x j)
  have hs : ∑ x, W x = 1 := by
    rw [show (∑ x, W x) = ∑ x : (∀ j : {j // j ≠ i}, Ω j), ∏ j : {j // j ≠ i}, w j.val (x j) from rfl, ← Fintype.prod_sum]
    simp only [hsum, Finset.prod_const_one]
  have hwE (x : ∀ j, Ω j) : (∏ j, w j (x j)) = w i (x i) * W (E x).2 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j (x j)) (Finset.mem_univ i)]
    congr 1
    exact Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp) (fun j => w j (x j))
  have hE (x : (∀ j : {j // j ≠ i}, Ω j)) (a b : Ω i) :
      Function.update (E.symm (a,x)) i b = E.symm (b,x) := by
    funext j
    by_cases h : j = i
    · subst j; simp [E, Equiv.piSplitAt]
    · simp [E, Equiv.piSplitAt, h]
  have hEq : (∑ x, (∏ j, w j (x j)) * F x) =
      ∑ x, W x * (∑ a, w i a * F (E.symm (a,x))) := by
    rw [Fintype.sum_equiv E _ (fun z => w i z.1 * W z.2 * F (E.symm z))]
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    · intro x
      rw [hwE, E.symm_apply_apply]
      rfl
  rw [hEq]
  have hFin (x : ∀ j : {j // j ≠ i}, Ω j) :
      (∑ a, w i a * F (E.symm (a,x))) ≤ C := by
    by_cases h : Nonempty (Ω i)
    · obtain ⟨a⟩ := h
      simpa only [hE] using hF (E.symm (a,x))
    · have := not_nonempty_iff.mp h
      have hz := hsum i
      simp at hz
  calc
    _ ≤ ∑ x, W x * C := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hFin x) (Finset.prod_nonneg fun j _ => hw j.val (x j))
    _ = C := by rw [← Finset.sum_mul, hs, one_mul]
theorem q_476 {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (bad : Ω → ι → Prop) [DecidableRel bad]
    (η : ℝ) (hbad : ∀ z, (∑ a, w a * if bad a z then (1 : ℝ) else 0) ≤ η) :
    ∃ a : Ω, ((Finset.univ.filter fun z => ¬ bad a z).card : ℝ) ≥
      (1-η) * Fintype.card ι := by
  classical
  have havg : (∑ a, w a * ((Finset.univ.filter fun z => bad a z).card : ℝ)) ≤
      η * Fintype.card ι := by
    simp_rw [← Finset.sum_boole, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum fun z _ => hbad z).trans_eq (by simp; ring)
  have hex : ∃ a : Ω, ((Finset.univ.filter fun z => bad a z).card : ℝ) ≤ η * Fintype.card ι := by
    by_contra h
    push Not at h
    have hp : ∃ a, 0 < w a := by
      by_contra h0
      push Not at h0
      have hz : ∀ a, w a = 0 := fun a => le_antisymm (h0 a) (hw a)
      simp [hz] at hsum
    obtain ⟨a,ha⟩ := hp
    have hlt : (∑ b, w b * (η * Fintype.card ι)) <
        ∑ b, w b * ((Finset.univ.filter fun z => bad b z).card : ℝ) := by
      apply Finset.sum_lt_sum
      · intro b _
        exact mul_le_mul_of_nonneg_left (h b).le (hw b)
      · exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left (h a) ha⟩
    rw [← Finset.sum_mul,hsum,one_mul] at hlt
    linarith
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,?_⟩
  have hc : (Finset.univ.filter fun z => bad a z).card +
      (Finset.univ.filter fun z => ¬ bad a z).card = Fintype.card ι := by
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun z => bad a z)
  have hcr : ((Finset.univ.filter fun z => bad a z).card : ℝ) +
      ((Finset.univ.filter fun z => ¬ bad a z).card : ℝ) = Fintype.card ι := by exact_mod_cast hc
  linarith
theorem q_417 {r : ℕ} (b : Fin r → ℝ) (hb : ∀ i, 0 ≤ b i)
    (ξ : ℝ) (hξ : 0 < ξ) :
    (if ∃ i, ξ < b i then (1 : ℝ) else 0) ≤ (∑ i, b i) / ξ := by
  classical
  split_ifs with h
  · obtain ⟨i,hi⟩ := h
    rw [le_div_iff₀ hξ, one_mul]
    exact hi.le.trans (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hb i) hξ.le
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
open scoped BigOperators
theorem q_381 {r : ℕ} {S : Type*} [Fintype S]
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1)
    (b : (∀ i, Ω i) → S → Fin r → ℝ)
    (hb : ∀ x z i, 0 ≤ b x z i) (η ξ : ℝ) (hξ : 0 < ξ)
    (hmean : ∀ z i x, (∑ a, w i a * b (Function.update x i a) z i) ≤ η) :
    ∃ x : ∀ i, Ω i,
      ((Finset.univ.filter fun z : S => ∀ i, b x z i ≤ ξ).card : ℝ) ≥
        (1 - (r : ℝ)*η/ξ) * Fintype.card S := by
  classical
  let W : (∀ i, Ω i) → ℝ := fun x => ∏ i, w i (x i)
  have hW : ∀ x, 0 ≤ W x := fun x => Finset.prod_nonneg fun i _ => hw i (x i)
  have hsumW : ∑ x, W x = 1 := by
    change (∑ x : ∀ i, Ω i, ∏ i, w i (x i)) = 1
    rw [← Fintype.prod_sum]
    simp only [hsum,Finset.prod_const_one]
  have hm (z : S) (i : Fin r) : ∑ x, W x * b x z i ≤ η :=
    q_426 w hw hsum i (fun x => b x z i) η (hmean z i)
  have hbad (z : S) :
      (∑ x, W x * if ∃ i, ξ < b x z i then (1 : ℝ) else 0) ≤ (r : ℝ)*η/ξ := by
    calc
      _ ≤ ∑ x, W x * ((∑ i, b x z i)/ξ) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (q_417 (b x z) (hb x z) ξ hξ) (hW x)
      _ = (∑ i, ∑ x, W x * b x z i)/ξ := by
        simp_rw [← mul_div_assoc,Finset.mul_sum]
        rw [← Finset.sum_div,Finset.sum_comm]
      _ ≤ (∑ _i : Fin r, η)/ξ := div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => hm z i) hξ.le
      _ = (r : ℝ)*η/ξ := by simp
  obtain ⟨x,hx⟩ := q_476 W hW hsumW
    (fun x z => ∃ i, ξ < b x z i) ((r : ℝ)*η/ξ) hbad
  refine ⟨x,?_⟩
  simpa only [not_exists,not_lt] using hx
lemma q_232 {K V σ α β : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (f : β → α)
    (n i : ℕ) (s : σ) (a : β) :
    q_17 (fun j t b => W j t (f b)) next n i s a =
      q_17 W next n i s (f a) := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [q_17,ih]
noncomputable def q_77 {r T : ℕ} {P : Fin r → Finset ℕ}
    {ell : Fin r → ℕ} (a : ∀ i, q_110 (P i) (ell i) T) : Fin r → Finset ℕ :=
  fun i => q_391 (a i)
lemma q_439 {r T : ℕ} {P : Fin r → Finset ℕ}
    {ell : Fin r → ℕ} (a : ∀ i, q_110 (P i) (ell i) T)
    (i : Fin r) (u : q_110 (P i) (ell i) T) :
    q_77 (Function.update a i u) = Function.update (q_77 a) i (q_391 u) := by
  funext j
  by_cases h : j = i
  · subst j; simp [q_77]
  · simp [q_77,Function.update_of_ne h]
theorem q_402 {K V σ S : Type*}
    [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype S]
    {r : ℕ} (P : Fin r → Finset ℕ) (ell : Fin r → ℕ) (T n : ℕ)
    (W : S → ℕ → σ → (Fin r → Finset ℕ) → Submodule K V)
    (next : S → ℕ → σ → Submodule K V → σ) (start : S → σ)
    (minor : S → σ → ℤ)
    (hW : ∀ z j s B i A A', A ⊆ A' →
      W z j s (Function.update B i A) ≤ W z j s (Function.update B i A'))
    (X ζ B η ξ : ℝ) (hX : 1 < X) (hζ : 0 < ζ) (hξ : 0 < ξ)
    (hp : ∀ i p, p ∈ P i → p.Prime)
    (hsmall : ∀ i p, p ∈ P i → X^ζ ≤ (p : ℝ))
    (hminor : ∀ z A, (∀ i, A i ⊆ P i) →
      ∀ t ∈ q_17 (W z) (next z) n 0 (start z) A,
        minor z t ≠ 0 ∧ |(minor z t : ℝ)| ≤ X^B)
    (hT : 0 < T) (hsize : ∀ i, ell i+T < (P i).card)
    (hη : ∀ i, (((Module.finrank K V+1)^n : ℕ) : ℝ)/T +
      (⌊(B*(n+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η) :
    ∃ A : Fin r → Finset ℕ,
      (∀ i, A i ⊆ P i ∧ ell i < (A i).card ∧ (A i).card ≤ ell i+T) ∧
      ((Finset.univ.filter fun z : S => ∀ i,
        ((∑ p ∈ A i,
          if (p : ℤ) ∣ ((q_17 (W z) (next z) n 0 (start z) A).map (minor z)).prod
          then (1 : ℝ) else 0) / (A i).card) ≤ ξ).card : ℝ) ≥
          (1-(r : ℝ)*η/ξ)*Fintype.card S := by
  classical
  let Ω := fun i => q_110 (P i) (ell i) T
  let w : ∀ i, Ω i → ℝ := fun i => q_367 (P i) (ell i) T
  let M := fun z A => ((q_17 (W z) (next z) n 0 (start z) A).map (minor z)).prod
  let b : (∀ i, Ω i) → S → Fin r → ℝ := fun a z i =>
    (∑ p ∈ q_77 a i, if (p : ℤ) ∣ M z (q_77 a) then (1 : ℝ) else 0) /
      (q_77 a i).card
  have hb : ∀ a z i, 0 ≤ b a z i := by
    intro a z i
    exact div_nonneg (Finset.sum_nonneg fun p _ => by split_ifs <;> positivity)
      (Nat.cast_nonneg _)
  have hmean : ∀ z i a, (∑ u, w i u * b (Function.update a i u) z i) ≤ η := by
    intro z i a
    let A₀ := q_77 a
    let Wi := fun j s A => W z j s (Function.update A₀ i A)
    let bad : Finset ℕ → Finset ℕ := fun A => (P i).filter fun p : ℕ =>
      (p : ℤ) ∣ M z (Function.update A₀ i A)
    have hm (A : Finset ℕ) (hA : A ⊆ P i) :
        ∀ t ∈ q_17 Wi (next z) n 0 (start z) A,
          minor z t ≠ 0 ∧ |(minor z t : ℝ)| ≤ X^B := by
      rw [q_232]
      apply hminor z
      intro j
      by_cases h : j = i
      · subst j; simpa using hA
      · simpa only [Function.update_of_ne h, A₀, q_77] using (q_435 (a j)).1
    have hdel := q_418 Wi (next z)
      (fun j s A A' hAA' => hW z j s A₀ i A A' hAA') (minor z) n (start z)
      (P i) (hp i) X ζ B hX hζ (hsmall i) hm (ell i) T hT (hsize i)
    dsimp only at hdel
    simp only [Wi, q_232] at hdel
    change ((∑ j ∈ Finset.range T, q_124 (P i) (ell i+j+1) bad) / T) ≤ _ at hdel
    have heq : (∑ u, w i u * b (Function.update a i u) z i) =
        (∑ j ∈ Finset.range T, q_124 (P i) (ell i+j+1) bad) / T := by
      rw [← q_415]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [w,b]
      rw [q_439, Function.update_self]
      congr 2
      apply Finset.sum_congr rfl
      intro p hpU
      have hpP := (q_435 u).1 hpU
      simp only [bad,Finset.mem_filter,hpP,true_and,A₀]
    rw [heq]
    exact hdel.trans (hη i)
  obtain ⟨a,ha⟩ := q_381 w
    (fun i => q_489 (P i) (ell i) T)
    (fun i => q_503 (P i) (ell i) T hT (hsize i).le)
    b hb η ξ hξ hmean
  refine ⟨q_77 a,?_,ha⟩
  intro i
  obtain ⟨hsub,hcard⟩ := q_435 (a i)
  refine ⟨hsub,?_,?_⟩
  · change ell i < (q_391 (a i)).card
    rw [hcard]; omega
  · change (q_391 (a i)).card ≤ ell i+T
    rw [hcard]
    have := (a i).1.isLt
    omega
open MvPolynomial
noncomputable def q_9 {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun j => j.val ≤ i).biUnion B
theorem q_345 {r : ℕ} {B C : Fin r → Finset ℕ}
    (hBC : ∀ j, B j ⊆ C j) (i : ℕ) :
    q_9 B i ⊆ q_9 C i := by
  classical
  intro p hp
  obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j,hj,hBC j hp⟩
def q_4 (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ) : ℕ → ℕ
  | 0 => e
  | i+1 => q_36 n A h (q_12 (d i) h (q_4 n d A h e i))
noncomputable def q_22 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (z : Fin n → ℤ) (i : ℕ) (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) : Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E) :=
  q_104 (q_98 G.points s.1 z (q_9 B i)) (d i) E
noncomputable def q_81 {n E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (W : Submodule ℂ (q_5 (σ := Fin n) (K := ℂ) E)) :
    Ideal (MvPolynomial (Fin n) ℂ) × q_1 n :=
  q_139 z s (q_86 G (d i) A h (q_4 n d A h e i) s.1 W)
def q_29 {n : ℕ} (G : KernelGeometry n) (h e : ℕ) (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n) : Prop :=
  q_466 h e s.1 ∧ s.2.On s.1 ∧ s.2.Bounded e G.height ∧ q_43 s z
theorem q_471 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (z : Fin n → ℤ) (i : ℕ) (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    {B C : Fin r → Finset ℕ} (hBC : ∀ j, B j ⊆ C j) :
    q_22 (E := E) G d z i s B ≤ q_22 G d z i s C :=
  q_319 (q_414 G.points s.1 z
    (q_345 hBC i))
theorem q_171 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (hz : z ∈ G.points) (i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : q_29 G h (q_4 n d A h e i) z s)
    (B : Fin r → Finset ℕ) :
    let W := q_22 (E := E) G d z i s B
    let t := q_81 G d A h e z i s W
    q_29 G h (q_4 n d A h e (i+1)) z t ∧
      t ∈ q_86 G (d i) A h (q_4 n d A h e i) s.1 W ∧
      s.1 ≤ t.1 ∧ q_26 (d i) E W ⊆ t.1 ∧
      q_0 t.1 ≤ q_0 s.1 ∧
      (¬ q_26 (d i) E W ⊆ s.1 → q_0 t.1 < q_0 s.1) := by
  classical
  dsimp only
  have hc := q_168 G (d i) A h (q_4 n d A h e i) s.1
    (q_22 (E := E) G d z i s B) hs.1
  have hzc : z ∈ q_98 G.points s.1 z (q_9 B i) := by
    exact Finset.mem_filter.mpr ⟨hz,hs.2.2.2.1,by simp⟩
  have hzF : ∀ p ∈ q_26 (d i) E (q_22 G d z i s B),
      eval (fun l => (z l : ℂ)) p = 0 := by
    rintro p ⟨v,hv,rfl,_⟩
    exact hv.2 z hzc
  have hsel := q_413 z s _ (hc.2.2 z hz hs.2.2.2.1 hzF)
  have hg := hc.2.1 _ hsel.1
  obtain ⟨⟨hp,hle,hdim,hdeg,hOn,hBound,_⟩,hF,hdim',hstrict⟩ := hg
  exact ⟨⟨⟨hp,hdim,hdeg⟩,hOn,hBound,hsel.2⟩,hsel.1,hle,hF,hdim',hstrict⟩
theorem q_481 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (hz : z ∈ G.points)
    (B : Fin r → Finset ℕ) (m i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : q_29 G h (q_4 n d A h e i) z s) :
    ∀ t ∈ q_17 (q_22 (E := E) G d z) (q_81 G d A h e z) m i s B,
      ∃ j, i ≤ j ∧ j ≤ i+m ∧ q_29 G h (q_4 n d A h e j) z t := by
  induction m generalizing i s with
  | zero =>
    intro t ht
    have ht : t = s := by simpa only [q_17,List.mem_singleton] using ht
    subst t
    exact ⟨i,le_rfl,by omega,hs⟩
  | succ m ih =>
    intro t ht
    rcases List.mem_cons.mp ht with hts | ht
    · subst t
      exact ⟨i,le_rfl,by omega,hs⟩
    · have hstep := (q_171 (E := E) G d A h e z hz i s hs B).1
      obtain ⟨j,hij,hj,htj⟩ := ih (i+1) _ hstep t ht
      exact ⟨j,by omega,by omega,htj⟩
open MvPolynomial
open scoped BigOperators
theorem q_269 (n : ℕ) (d : ℕ → ℕ) (A h e m E : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ,
      ∀ (G : KernelGeometry n) (z : Fin n → ℤ), z ∈ G.points →
      ∀ (s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n),
        q_29 G h e z s → ∀ (r : ℕ) (B : Fin r → Finset ℕ),
      ∀ t ∈ q_17 (q_22 (E := E) G d z) (q_81 G d A h e z) m 0 s B,
        eval z t.2.minor ≠ 0 ∧ |((eval z t.2.minor : ℤ) : ℝ)| ≤ C*G.height^b := by
  classical
  let D := (Finset.range (m+1)).sup (q_4 n d A h e)
  obtain ⟨C,hC,b,hb⟩ := q_315 n D
  refine ⟨C,hC,b,?_⟩
  intro G z hz s hs r B t ht
  obtain ⟨j,_,hj,hjt⟩ := q_481 (E := E) G d A h e z hz B m 0 s hs t ht
  have hD : q_4 n d A h e j ≤ D :=
    Finset.le_sup (f := q_4 n d A h e) (Finset.mem_range.mpr (by omega))
  exact ⟨hjt.2.2.2.2,hb t.2 G.height G.one_le_height (hjt.2.2.1.mono hD) z (G.bounded z hz)⟩
theorem q_405 (n : ℕ) (d : ℕ → ℕ) (A h e m E : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ,
    ∀ (G : KernelGeometry n)
      (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n),
      (∀ z, q_29 G h e z.val (start z)) →
    ∀ (r : ℕ) (P : Fin r → Finset ℕ) (ell : Fin r → ℕ) (T : ℕ)
      (X ζ w η ξ : ℝ), 1 < X → C ≤ X → 0 ≤ w → G.height ≤ X^w → 0 < ζ → 0 < ξ →
      (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → X^ζ ≤ (p : ℝ)) →
      0 < T → (∀ i, ell i+T < (P i).card) →
      (∀ i, ((((E+n).choose n+1)^m : ℕ) : ℝ)/T +
        (⌊((w*b+1)*(m+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η) →
    ∃ B : Fin r → Finset ℕ,
      (∀ i, B i ⊆ P i ∧ ell i < (B i).card ∧ (B i).card ≤ ell i+T) ∧
      ((Finset.univ.filter fun z : G.points => ∀ i,
        ((∑ p ∈ B i,
          if (p : ℤ) ∣ ((q_17 (q_22 (E := E) G d z.val)
            (q_81 G d A h e z.val) m 0 (start z) B).map
            (fun t => eval z.val t.2.minor)).prod
          then (1 : ℝ) else 0) / (B i).card) ≤ ξ).card : ℝ) ≥
            (1-(r : ℝ)*η/ξ)*G.points.card := by
  classical
  obtain ⟨C,hC,b,hb⟩ := q_269 n d A h e m E
  refine ⟨C,hC,b,?_⟩
  intro G start hs r P ell T X ζ w η ξ hX hCX hw hheight hζ hξ hp hsmall hT hsize hη
  let := q_70 (n := n) (K := ℂ) E
  have hmono : ∀ (z : G.points) j s (B : Fin r → Finset ℕ) i U U', U ⊆ U' →
      q_22 (E := E) G d z.val j s (Function.update B i U) ≤
      q_22 G d z.val j s (Function.update B i U') := by
    intro z j s B i U U' hUU'
    apply q_471
    intro k
    by_cases hk : k = i
    · subst k; simpa using hUU'
    · simp only [Function.update_of_ne hk]
      exact Finset.Subset.refl _
  have hminor : ∀ (z : G.points) B, (∀ i, B i ⊆ P i) →
      ∀ t ∈ q_17 (q_22 (E := E) G d z.val)
          (q_81 G d A h e z.val) m 0 (start z) B,
        eval z.val t.2.minor ≠ 0 ∧ |((eval z.val t.2.minor : ℤ) : ℝ)| ≤ X^(w*b+1) := by
    intro z B _ t ht
    have ht' := hb G z.val z.property (start z) (hs z) r B t ht
    refine ⟨ht'.1,ht'.2.trans ?_⟩
    calc
      C*G.height^b ≤ X*(X^w)^b := mul_le_mul hCX
        (pow_le_pow_left₀ (zero_le_one.trans G.one_le_height) hheight b)
        (pow_nonneg (zero_le_one.trans G.one_le_height) b) (zero_lt_one.trans hX).le
      _ = X^(w*b+1) := by
        rw [Real.rpow_add (zero_lt_one.trans hX), Real.rpow_one,
          Real.rpow_mul (zero_lt_one.trans hX).le,Real.rpow_natCast,mul_comm]
  have hη' : ∀ i, (((Module.finrank ℂ (q_5 (σ := Fin n) (K := ℂ) E)+1)^m : ℕ) : ℝ)/T +
      (⌊((w*b+1)*(m+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η := by
    simpa only [q_353] using hη
  simpa only [Fintype.card_coe] using
    q_402 P ell T m (fun z => q_22 (E := E) G d z.val)
      (fun z => q_81 G d A h e z.val) start
      (fun z t => eval z.val t.2.minor) hmono X ζ (w*b+1) η ξ hX hζ hξ hp hsmall hminor
      hT hsize hη'
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
open MvPolynomial
open scoped Matrix
theorem q_157 {σ R : Type*} [CommRing R]
    (q : R) (P : MvPolynomial σ R) (x y : σ → R)
    (hxy : ∀ i, q ∣ x i - y i) : q ∣ eval x P - eval y P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hP hQ
  | mul_X P i hP =>
    have h := dvd_add (dvd_mul_of_dvd_left hP (x i))
      (dvd_mul_of_dvd_right (hxy i) (eval y P))
    simpa only [map_mul, eval_X] using (show q ∣ eval x P * x i - eval y P * y i by
      convert h using 1; ring)
theorem q_423 {σ R : Type*} [Fintype σ] [CommRing R]
    (q : R) (s : ℕ) (P : MvPolynomial σ R) (x y : σ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ i, q ∣ y i)
    (hxy : ∀ i, q ^ s ∣ x i - y i) :
    q ^ (s + 1) ∣ eval x P - eval y P -
      ∑ i, eval (fun _ => 0) (pderiv i P) * (x i - y i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    convert dvd_add hP hQ using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X P i hP =>
    have h1 : q ^ (s + 1) ∣ (eval x P - eval y P) * x i := by
      simpa only [pow_succ] using mul_dvd_mul (q_157 (q ^ s) P x y hxy) (hx i)
    have h2 : q ^ (s + 1) ∣ (eval y P - eval (fun _ => 0) P) * (x i - y i) := by
      have h0 : q ∣ eval y P - eval (fun _ => 0) P :=
        q_157 q P y (fun _ => 0) (by simpa using hy)
      simpa only [pow_succ, mul_comm q] using mul_dvd_mul h0 (hxy i)
    have hs : (∑ j, eval (fun _ => 0) (pderiv j (P * X i)) * (x j - y j)) =
        eval (fun _ => 0) P * (x i - y i) := by
      simp [pderiv_X, Pi.single_apply, apply_ite]
    rw [hs, map_mul, map_mul, eval_X, eval_X]
    convert dvd_add h1 h2 using 1; ring
theorem q_213 {σ τ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (F : σ → MvPolynomial τ R) (x : τ → R) :
    eval x (eval₂ C F P) = eval (fun i => eval x (F i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [eval₂_mul, hP]
noncomputable def q_21 {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R) : ℕ → κ → MvPolynomial ι R
  | 0, _ => 0
  | n + 1, j => eval₂ C (Sum.elim X (q_21 Φ n)) (Φ j)
 theorem q_66 {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R) (n : ℕ) (x : ι → R) (j : κ) :
    eval x (q_21 Φ (n + 1) j) =
      eval (Sum.elim x (fun a => eval x (q_21 Φ n a))) (Φ j) := by
  rw [q_21, q_213]
  congr 2
  funext a
  cases a <;> simp
 theorem q_190 {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0) (n : ℕ) (j : κ) :
    eval (fun _ => 0) (q_21 Φ n j) = 0 := by
  induction n generalizing j with
  | zero => simp [q_21]
  | succ n ih =>
    rw [q_66]
    have hn : (Sum.elim (fun _ : ι => (0 : R))
        (fun a => eval (fun _ => 0) (q_21 Φ n a))) = (fun _ => 0) := by
      funext a
      cases a with
      | inl a => rfl
      | inr a => exact ih a
    rw [hn]
    exact hzero j
theorem q_189 {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (s : ℕ) (x : ι → R) (y z : κ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ j, q ∣ y j) (hz : ∀ j, q ∣ z j)
    (hyz : ∀ j, q ^ s ∣ y j - z j) (j : κ) :
    q ^ (s + 1) ∣ eval (Sum.elim x y) (Φ j) - eval (Sum.elim x z) (Φ j) := by
  have hv : ∀ i, q ∣ (Sum.elim x y) i := by intro i; cases i <;> simp_all
  have hw : ∀ i, q ∣ (Sum.elim x z) i := by intro i; cases i <;> simp_all
  have hvw : ∀ i, q ^ s ∣ (Sum.elim x y) i - (Sum.elim x z) i := by
    intro i
    cases i <;> simp_all
  have h := q_423 q s (Φ j) (Sum.elim x y) (Sum.elim x z) hv hw hvw
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self,
    mul_zero, hlinear, zero_mul, Finset.sum_const_zero, add_zero, sub_zero] using h
theorem q_383 {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (y : κ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ j, q ∣ y j)
    (hfix : ∀ j, eval (Sum.elim x y) (Φ j) = y j) (n : ℕ) (j : κ) :
    q ^ (n + 1) ∣ y j - eval x (q_21 Φ n j) := by
  induction n generalizing j with
  | zero => simpa only [q_21, map_zero, sub_zero, zero_add, pow_one] using hy j
  | succ n ih =>
    have hn : ∀ a, q ∣ eval x (q_21 Φ n a) := by
      intro a
      have h := q_157 q (q_21 Φ n a) x (fun _ => 0)
        (by simpa only [sub_zero] using hx)
      simpa only [q_190 Φ hzero, sub_zero] using h
    have h := q_189 Φ hlinear q (n + 1) x y
      (fun a => eval x (q_21 Φ n a)) hx hy hn
      ih j
    rwa [hfix, ← q_66] at h
noncomputable def q_20 {ι κ R : Type*} [CommRing R]
    (G : κ → MvPolynomial (ι ⊕ κ) R) : Matrix κ κ R :=
  Matrix.of (fun j a => eval (fun _ => 0) (pderiv (Sum.inr a) (G j)))
noncomputable def q_34 {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (j : κ) : MvPolynomial (ι ⊕ κ) R :=
  X (Sum.inr j) - ∑ a, C ((q_20 G)⁻¹ j a) * G a
theorem q_101 {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0) (j : κ) :
    eval (fun _ => 0) (q_34 G j) = 0 := by
  simp only [q_34, map_sub, map_sum, map_mul, eval_X, eval_C,
    hzero, mul_zero, Finset.sum_const_zero, sub_zero]
theorem q_134 {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hunit : IsUnit (q_20 G).det) (j a : κ) :
    eval (fun _ => 0) (pderiv (Sum.inr a) (q_34 G j)) = 0 := by
  classical
  have hmat := congrArg (fun M : Matrix κ κ R => M j a)
    (Matrix.nonsing_inv_mul (q_20 G) hunit)
  simp only [Matrix.mul_apply, Matrix.one_apply] at hmat
  have hs : (∑ b, (q_20 G)⁻¹ j b *
      eval (fun _ => 0) (pderiv (Sum.inr a) (G b))) = if j = a then 1 else 0 := hmat
  simp only [q_34, map_sub, map_sum, pderiv_mul, pderiv_C,
    zero_mul, zero_add, pderiv_X, Pi.single_apply, map_mul, eval_C]
  rw [hs]
  by_cases h : j = a <;> simp [h]
theorem q_301 {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (x : ι → R) (y : κ → R)
    (hroot : ∀ j, eval (Sum.elim x y) (G j) = 0) (j : κ) :
    eval (Sum.elim x y) (q_34 G j) = y j := by
  simp [q_34, hroot]
theorem q_238 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (q_20 G).det) (q : R) (n : ℕ) :
    ∃ F : κ → MvPolynomial ι R,
      (∀ j, eval (fun _ => 0) (F j) = 0) ∧
      ∀ (x : ι → R) (y : κ → R), (∀ i, q ∣ x i) → (∀ j, q ∣ y j) →
        (∀ j, eval (Sum.elim x y) (G j) = 0) →
        ∀ j, q ^ (n + 1) ∣ y j - eval x (F j) := by
  refine ⟨q_21 (q_34 G) n, ?_, ?_⟩
  · exact q_190 _ (q_101 G hzero) n
  · intro x y hx hy hroot j
    exact q_383 _ (q_101 G hzero)
      (q_134 G hunit) q x y hx hy
      (q_301 G x y hroot) n j
theorem q_126 {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) (n : ℕ) (j : κ) :
    q ∣ eval x (q_21 Φ n j) := by
  have h := q_157 q (q_21 Φ n j) x (fun _ => 0)
    (by simpa only [sub_zero] using hx)
  simpa only [q_190 Φ hzero, sub_zero] using h
theorem q_206 {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) (n : ℕ) (j : κ) :
    q ^ (n + 1) ∣ eval x (q_21 Φ (n + 1) j) -
      eval x (q_21 Φ n j) := by
  induction n generalizing j with
  | zero =>
    simpa only [zero_add, pow_one, q_21, map_zero, sub_zero] using
      q_126 Φ hzero q x hx 1 j
  | succ n ih =>
    rw [q_66, q_66 Φ n]
    exact q_189 Φ hlinear q (n + 1) x
      (fun j => eval x (q_21 Φ (n + 1) j))
      (fun j => eval x (q_21 Φ n j)) hx
      (q_126 Φ hzero q x hx (n + 1))
      (q_126 Φ hzero q x hx n) ih j
theorem q_382 {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) {n m : ℕ} (hnm : n ≤ m) (j : κ) :
    q ^ (n + 1) ∣ eval x (q_21 Φ m j) -
      eval x (q_21 Φ n j) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have hs := (pow_dvd_pow q (Nat.add_le_add_right hnm 1)).trans
      (q_206 Φ hzero hlinear q x hx m j)
    simpa only [sub_add_sub_cancel] using dvd_add hs ih
theorem q_204 {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [CommRing K] (Φ : κ → MvPolynomial (ι ⊕ κ) (PowerSeries K))
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (x : ι → PowerSeries K) (hx : ∀ i, PowerSeries.X ∣ x i) :
    ∃ y : κ → PowerSeries K, (∀ j, PowerSeries.constantCoeff (y j) = 0) ∧
      ∀ j, eval (Sum.elim x y) (Φ j) = y j := by
  let v := fun n j => eval x (q_21 Φ n j)
  let y : κ → PowerSeries K := fun j =>
    PowerSeries.mk (fun n => PowerSeries.coeff n (v n j))
  have happ : ∀ n j, PowerSeries.X ^ (n + 1) ∣ y j - v n j := by
    intro n j
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    have he := PowerSeries.X_pow_dvd_iff.mp
      (q_382 Φ hzero hlinear PowerSeries.X x hx
        (Nat.le_of_lt_succ hi) j) i (Nat.lt_succ_self i)
    change PowerSeries.coeff i (v n j - v i j) = 0 at he
    simp only [map_sub] at he
    simp only [map_sub, y, PowerSeries.coeff_mk]
    exact sub_eq_zero.mpr (sub_eq_zero.mp he).symm
  refine ⟨y, ?_, ?_⟩
  · intro j
    have h := happ 0 j
    simpa only [zero_add, pow_one, v, q_21, map_zero, sub_zero,
      PowerSeries.X_dvd_iff] using h
  · intro j
    apply sub_eq_zero.mp
    apply PowerSeries.ext
    intro n
    have hdiff : ∀ a, PowerSeries.X ^ (n + 1) ∣
        (Sum.elim x y) a - (Sum.elim x (v n)) a := by
      intro a
      cases a with
      | inl i => simp
      | inr j => exact happ n j
    have h1 := q_157 (PowerSeries.X ^ (n + 1)) (Φ j)
      (Sum.elim x y) (Sum.elim x (v n)) hdiff
    have h2 := q_206 Φ hzero hlinear PowerSeries.X x hx n j
    have h3 := dvd_neg.mpr (happ n j)
    have hs := dvd_add (dvd_add h1 h2) h3
    have ht : PowerSeries.X ^ (n + 1) ∣ eval (Sum.elim x y) (Φ j) - y j := by
      convert hs using 1
      rw [q_66]
      dsimp [v]
      ring
    have he := PowerSeries.X_pow_dvd_iff.mp ht n (Nat.lt_succ_self n)
    simpa only [map_zero] using he
theorem q_329 {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hunit : IsUnit (q_20 G).det) (x : ι → R) (y : κ → R)
    (hfix : ∀ j, eval (Sum.elim x y) (q_34 G j) = y j) :
    ∀ j, eval (Sum.elim x y) (G j) = 0 := by
  let v : κ → R := fun j => eval (Sum.elim x y) (G j)
  have hv : (q_20 G)⁻¹ *ᵥ v = 0 := by
    funext j
    have h := hfix j
    simp only [q_34, map_sub, map_sum, map_mul, eval_X, eval_C] at h
    simpa only [Matrix.mulVec, dotProduct, v, Pi.zero_apply] using (sub_eq_self.mp h)
  have h := congrArg (Matrix.mulVec (q_20 G)) hv
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact fun j => congrFun h j
theorem q_215 {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [CommRing K] (G : κ → MvPolynomial (ι ⊕ κ) (PowerSeries K))
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (q_20 G).det)
    (x : ι → PowerSeries K) (hx : ∀ i, PowerSeries.X ∣ x i) :
    ∃ y : κ → PowerSeries K, (∀ j, PowerSeries.constantCoeff (y j) = 0) ∧
      ∀ j, eval (Sum.elim x y) (G j) = 0 := by
  obtain ⟨y, hy, hfix⟩ := q_204 (q_34 G)
    (q_101 G hzero) (q_134 G hunit) x hx
  exact ⟨y, hy, q_329 G hunit x y hfix⟩
noncomputable def q_28 {κ R : Type*} [CommRing R]
    (a : κ → R) : MvPolynomial κ R →+* MvPolynomial (Unit ⊕ κ) R :=
  eval₂Hom C (fun i => X (Sum.inr i) + C (a i))
@[simp] theorem eval_shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) (p : MvPolynomial κ R) (z : Unit ⊕ κ → R) :
    eval z (q_28 a p) = eval (fun i => z (Sum.inr i) + a i) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [q_28]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [q_28]
theorem q_202 {κ R : Type*} [CommRing R]
    (a : κ → R) (p : MvPolynomial κ R) (i : κ) :
    pderiv (Sum.inr i) (q_28 a p) =
      q_28 a (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [q_28]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    simp only [q_28, eval₂Hom_X', map_add, pderiv_X,
      pderiv_C, add_zero, Pi.single_apply, Sum.inr.injEq]
    split_ifs <;> simp
theorem q_216 {κ K : Type*} [Fintype κ] [DecidableEq κ]
    [Field K] (f : κ → MvPolynomial κ K) (a : κ → K)
    (ha : ∀ j, eval a (f j) = 0)
    (hJ : (Matrix.of (fun i j => eval a (pderiv j (f i)))).det ≠ 0) (D : ℕ) :
    ∃ y : κ → PowerSeries K,
      (∀ j, PowerSeries.constantCoeff (y j) = a j) ∧
      ∀ j, eval₂ PowerSeries.C y (f j) + PowerSeries.X * y j ^ (D + 1) = 0 := by
  let a' : κ → PowerSeries K := fun j => PowerSeries.C (a j)
  let f' : κ → MvPolynomial κ (PowerSeries K) := fun j => map PowerSeries.C (f j)
  let G : κ → MvPolynomial (Unit ⊕ κ) (PowerSeries K) := fun j =>
    q_28 a' (f' j) +
      X (Sum.inl ()) * (X (Sum.inr j) + C (a' j)) ^ (D + 1)
  have hzero : ∀ j, eval (fun _ => 0) (G j) = 0 := by
    intro j
    simp only [G, map_add, eval_shiftedParameterPolynomial, zero_add, map_mul,
      eval_X, zero_mul, add_zero, f', a']
    rw [← eval₂_eq_eval_map]
    simpa only [Function.comp_def, ha, map_zero] using
      (eval₂_comp PowerSeries.C a (f j)).symm
  have hjac : q_20 G =
      (Matrix.of (fun i j => eval a (pderiv j (f i)))).map PowerSeries.C := by
    apply Matrix.ext
    intro i j
    simp only [q_20, Matrix.of_apply, Matrix.map_apply, G, map_add,
      q_202, pderiv_mul, pderiv_X, Pi.single_apply,
      Sum.inl_ne_inr, ite_false, zero_mul, zero_add, eval_X, map_mul, map_add,
      zero_mul, add_zero, eval_shiftedParameterPolynomial, zero_add, f', pderiv_map, a']
    rw [← eval₂_eq_eval_map]
    exact (eval₂_comp PowerSeries.C a (pderiv j (f i))).symm
  have hunit : IsUnit (q_20 G).det := by
    rw [hjac, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hJ).map PowerSeries.C
  obtain ⟨v, hv, hroot⟩ := q_215 G hzero hunit
    (fun _ => PowerSeries.X) (fun _ => dvd_refl _)
  refine ⟨fun j => v j + a' j, ?_, ?_⟩
  · intro j
    simp [hv, a']
  · intro j
    have h := hroot j
    simp only [G, map_add, eval_shiftedParameterPolynomial, Sum.elim_inr, map_mul,
      eval_X, Sum.elim_inl, map_pow, eval_C, f', ← eval₂_eq_eval_map] at h
    exact h
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial MonomialOrder
open scoped MonomialOrder
theorem q_297 {n : ℕ} {K : Type*} [Field K]
    (D : ℕ) (q : Fin n → MvPolynomial (Fin n) K)
    (hq : ∀ i, (q i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    ∃ (g : Fin n →₀ MvPolynomial (Fin n) K) (r : MvPolynomial (Fin n) K),
      p = Finsupp.linearCombination _ (fun i => X i ^ (D + 1) - q i) g + r ∧
      ∀ m ∈ r.support, ∀ i, m i ≤ D := by
  classical
  have hlt : ∀ i, degLex.degree (q i) ≺[degLex]
      degLex.degree (X i ^ (D + 1) : MvPolynomial (Fin n) K) := by
    intro i
    apply lt_of_not_ge
    intro h
    have ht := MvPolynomial.degLex_totalDegree_monotone h
    simp only [MvPolynomial.totalDegree_X_pow] at ht
    exact Nat.not_succ_le_self D (ht.trans (hq i))
  have hdeg : ∀ i, degLex.degree (X i ^ (D + 1) - q i) =
      Finsupp.single i (D + 1) := by
    intro i
    rw [degLex.degree_sub_of_lt (hlt i), X_pow_eq_monomial,
      degLex.degree_monomial, if_neg one_ne_zero]
  have hun : ∀ i, IsUnit (degLex.leadingCoeff (X i ^ (D + 1) - q i)) := by
    intro i
    rw [degLex.leadingCoeff_sub_of_lt (hlt i), X_pow_eq_monomial,
      degLex.leadingCoeff_monomial]
    exact isUnit_one
  obtain ⟨g, r, he, _, hr⟩ := MonomialOrder.div hun p
  refine ⟨g, r, he, ?_⟩
  intro m hm i
  have hh := hr m hm i
  rw [hdeg i] at hh
  have : ¬ (D + 1 ≤ m i) := by
    intro h
    apply hh
    exact Finsupp.single_le_iff.mpr h
  omega
theorem q_346 {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (D : ℕ) (q : Fin n → MvPolynomial (Fin n) K)
    (hq : ∀ i, (q i).totalDegree ≤ D) (z : ι → Fin n → K)
    (hz : Function.Injective z)
    (hroot : ∀ a i, z a i ^ (D + 1) = eval (z a) (q i)) :
    Fintype.card ι ≤ (D + 1) ^ n := by
  classical
  let ex : (Fin n → Fin (D + 1)) → (Fin n →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm (fun i => (m i).val)
  let b : (Fin n → Fin (D + 1)) → (ι → K) := fun m a =>
    eval (z a) (monomial (ex m) 1)
  let E : MvPolynomial (Fin n) K →ₗ[K] (ι → K) :=
    { toFun := fun p a => eval (z a) p
      map_add' := by intro p r; ext a; simp
      map_smul' := by intro c p; ext a; simp [smul_eq_C_mul] }
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨p, hp⟩ := q_451 z hz v
    obtain ⟨g, r, he, hr⟩ := q_297 D q hq p
    have her : E r = v := by
      funext a
      have h := congrArg (eval (z a)) he
      simp only [map_add, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, map_sum, map_mul, map_sub, map_pow, eval_X, hroot,
        sub_self, mul_zero, Finset.sum_const_zero, zero_add, hp] at h
      exact h.symm
    rw [← her, r.as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    let m' : Fin n → Fin (D + 1) := fun i => ⟨m i, Nat.lt_succ_of_le (hr m hm i)⟩
    have hex : ex m' = m := by ext i; rfl
    have hb : E (monomial m (r.coeff m)) = r.coeff m • b m' := by
      funext a
      simp only [E, LinearMap.coe_mk, AddHom.coe_mk, b, hex, Pi.smul_apply,
        smul_eq_mul, eval_monomial, one_mul]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m', rfl⟩)
  have h := finrank_le_of_span_eq_top hspan
  simpa only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin] using h
end
section
open MvPolynomial
theorem q_205 {n : ℕ} {K ι : Type*} [Field K]
    [Fintype ι] (D : ℕ) (f : Fin n → MvPolynomial (Fin n) K)
    (hf : ∀ i, (f i).totalDegree ≤ D) (a : ι → Fin n → K)
    (hinj : Function.Injective a) (ha : ∀ b i, eval (a b) (f i) = 0)
    (hJ : ∀ b, (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))).det ≠ 0) :
    Fintype.card ι ≤ (D + 1) ^ n := by
  classical
  choose y hy hyr using fun b => q_216 f (a b) (ha b) (hJ b) D
  let L := FractionRing (PowerSeries K)
  let inc : PowerSeries K →+* L := algebraMap _ _
  let c : K →+* L := inc.comp PowerSeries.C
  let T : L := inc PowerSeries.X
  let z : ι → Fin n → L := fun b i => inc (y b i)
  have hinc : Function.Injective inc := IsFractionRing.injective _ _
  have ht : T ≠ 0 := by
    exact fun h => PowerSeries.X_ne_zero (hinc (h.trans inc.map_zero.symm))
  have hz : Function.Injective z := by
    intro b b' h
    apply hinj
    funext i
    have hyy := hinc (congrFun h i)
    have hcc := congrArg PowerSeries.constantCoeff hyy
    simpa only [hy] using hcc
  let q : Fin n → MvPolynomial (Fin n) L := fun i => (-T⁻¹) • map c (f i)
  have hq : ∀ i, (q i).totalDegree ≤ D := by
    intro i
    apply (totalDegree_smul_le _ _).trans
    have hmap : (map c (f i)).totalDegree ≤ (f i).totalDegree :=
      Finset.sup_mono (support_map_subset c (f i))
    exact hmap.trans (hf i)
  apply q_346 D q hq z hz
  intro b i
  have h := congrArg inc (hyr b i)
  simp only [map_add, map_mul, map_pow, map_zero, eval₂_comp_left] at h
  change eval₂ c (z b) (f i) + T * z b i ^ (D + 1) = 0 at h
  change z b i ^ (D + 1) = eval (z b) ((-T⁻¹) • map c (f i))
  rw [smul_eq_C_mul, map_mul, eval_C, ← eval₂_eq_eval_map]
  apply mul_left_cancel₀ ht
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ ht, neg_one_mul]
  exact eq_neg_of_add_eq_zero_right h
theorem q_208 {σ τ K : Type*} [CommSemiring K]
    (F : σ → MvPolynomial τ K) (hF : ∀ i, (F i).totalDegree ≤ 1)
    (p : MvPolynomial σ K) :
    (eval₂ C F p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, eval₂_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [eval₂_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ m.support, (F i ^ m i).totalDegree) ≤
        ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hF i))
    _ ≤ p.totalDegree := le_totalDegree hm
noncomputable def q_123 {ι κ K : Type*} [CommSemiring K] (x : ι → K) :
    MvPolynomial (ι ⊕ κ) K →+* MvPolynomial κ K :=
  eval₂Hom C (Sum.elim (fun i => C (x i)) X)
@[simp] theorem eval_partialEval {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (y : κ → K) (p : MvPolynomial (ι ⊕ κ) K) :
    eval y (q_123 x p) = eval (Sum.elim x y) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [q_123]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, hp]
    congr 1
    cases a <;> simp [q_123]
theorem q_316 {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (p : MvPolynomial (ι ⊕ κ) K) :
    (q_123 x p).totalDegree ≤ p.totalDegree := by
  apply q_208
  intro a
  cases a with
  | inl i => simp
  | inr j =>
    simpa [X] using
      totalDegree_monomial_le (Finsupp.single j 1) (1 : K)
theorem q_483 {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (p : MvPolynomial (ι ⊕ κ) K) (j : κ) :
    pderiv j (q_123 x p) = q_123 x (pderiv (Sum.inr j) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [q_123]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    cases a with
    | inl i => simp [q_123]
    | inr i =>
      simp only [q_123, eval₂Hom_X', Sum.elim_inr, pderiv_X,
        Pi.single_apply, Sum.inr.injEq]
      split_ifs <;> simp
end
open scoped BigOperators
theorem q_306 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (good : ∀ i, Finset (α i)) (A M h N b : ℕ)
    (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hall : ∀ i, Fintype.card (α i) ≤ M^N)
    (hgood : ∀ i, (good i).card ≤ A*M^h) :
    let R := Finset.univ.filter fun x : ∀ i, α i =>
      (Finset.univ.filter fun i => x i ∉ good i).card ≤ b
    R.card ≤ 2^Fintype.card ι * A^Fintype.card ι *
      M^(h*Fintype.card ι+N*b) := by
  classical
  let U : Finset (Finset ι) := Finset.univ.powerset.filter fun u => u.card ≤ b
  let C : Finset ι → Finset (∀ i, α i) := fun u =>
    Fintype.piFinset fun i => if i ∈ u then Finset.univ else good i
  have hbase : 1 ≤ A*M^h := by simpa using Nat.mul_le_mul hA (one_le_pow₀ hM (n := h))
  have hC (u : Finset ι) (hu : u ∈ U) :
      (C u).card ≤ A^Fintype.card ι*M^(h*Fintype.card ι+N*b) := by
    have hub : u.card ≤ b := (Finset.mem_filter.mp hu).2
    calc
      (C u).card = ∏ i, (if i ∈ u then Fintype.card (α i) else (good i).card) := by
        simp only [C,Fintype.card_piFinset]
        apply Finset.prod_congr rfl
        intro i _
        split_ifs <;> simp
      _ ≤ ∏ i, (A*M^h) * (if i ∈ u then M^N else 1) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro i _
        by_cases hi : i ∈ u
        · simp only [hi,ite_true]
          exact (hall i).trans (by simpa using Nat.mul_le_mul_right (M^N) hbase)
        · simpa only [hi,ite_false,mul_one] using hgood i
      _ = (A*M^h)^Fintype.card ι * (M^N)^u.card := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ (A*M^h)^Fintype.card ι * (M^N)^b :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (pow_pos (by omega : 0 < M) N) hub)
      _ = A^Fintype.card ι*M^(h*Fintype.card ι+N*b) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
  have hsub : (Finset.univ.filter fun x : ∀ i, α i =>
      (Finset.univ.filter fun i => x i ∉ good i).card ≤ b) ⊆ U.biUnion C := by
    intro x hx
    let u := Finset.univ.filter fun i => x i ∉ good i
    refine Finset.mem_biUnion.mpr ⟨u, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        (Finset.mem_filter.mp hx).2⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hi : i ∈ u
      · simp only [hi,ite_true,Finset.mem_univ]
      · have hg : x i ∈ good i := by simpa [u] using hi
        simpa only [hi,ite_false] using hg
  calc
    _ ≤ (U.biUnion C).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (C u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, A^Fintype.card ι*M^(h*Fintype.card ι+N*b) :=
      Finset.sum_le_sum hC
    _ = U.card * (A^Fintype.card ι*M^(h*Fintype.card ι+N*b)) := by simp
    _ ≤ 2^Fintype.card ι * (A^Fintype.card ι*M^(h*Fintype.card ι+N*b)) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = _ := by ring
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
theorem q_249 {κ β K : Type*} [Fintype κ] [DecidableEq κ] [Fintype β]
    [Field K] (D : ℕ) (f : κ → MvPolynomial κ K)
    (hf : ∀ i, (f i).totalDegree ≤ D) (a : β → κ → K)
    (hinj : Function.Injective a) (ha : ∀ b i, eval (a b) (f i) = 0)
    (hJ : ∀ b, (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))).det ≠ 0) :
    Fintype.card β ≤ (D+1)^Fintype.card κ := by
  classical
  let e := Fintype.equivFin κ
  let f' : Fin (Fintype.card κ) → MvPolynomial (Fin (Fintype.card κ)) K :=
    fun i => rename e (f (e.symm i))
  let a' : β → Fin (Fintype.card κ) → K := fun b i => a b (e.symm i)
  have hev (b : β) (p : MvPolynomial κ K) : eval (a' b) (rename e p) = eval (a b) p := by
    rw [eval_rename]
    simp [a',Function.comp_def]
  apply q_205 D f'
    (fun i => (totalDegree_rename_le e _).trans (hf (e.symm i))) a'
  · intro b c hab
    apply hinj
    funext j
    simpa [a'] using congrFun hab (e j)
  · intro b i
    exact (hev b _).trans (ha b (e.symm i))
  · intro b
    have heq : (Matrix.of (fun i j => eval (a' b) (pderiv j (f' i)))) =
        Matrix.reindex e e (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))) := by
      ext i j
      change eval (a' b) (pderiv j (rename e (f (e.symm i)))) = _
      rw [← e.apply_symm_apply j, pderiv_rename e.injective, hev]
      simp [Matrix.reindex,Matrix.of_apply]
    rw [heq,Matrix.det_reindex_self]
    exact hJ b
theorem q_364 {ι κ β K : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [Fintype β] [Field K] [Fintype K]
    (D : ℕ) (G : κ → MvPolynomial (ι ⊕ κ) K)
    (hG : ∀ j, (G j).totalDegree ≤ D) (z : β → (ι ⊕ κ) → K)
    (hinj : Function.Injective z) (hz : ∀ b j, eval (z b) (G j) = 0)
    (hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0) :
    Fintype.card β ≤ Fintype.card K ^ Fintype.card ι * (D+1)^Fintype.card κ := by
  classical
  let free : β → ι → K := fun b i => z b (Sum.inl i)
  have hfiber (x : ι → K) : Fintype.card {b // free b = x} ≤ (D+1)^Fintype.card κ := by
    let a : {b // free b = x} → κ → K := fun b j => z b.val (Sum.inr j)
    have heq (b : {b // free b = x}) : Sum.elim x (a b) = z b.val := by
      funext j
      cases j with
      | inl i => exact (congrFun b.property i).symm
      | inr j => rfl
    apply q_249 D (fun j => q_123 x (G j))
      (fun j => (q_316 x (G j)).trans (hG j)) a
    · intro b b' h
      apply Subtype.ext
      apply hinj
      rw [← heq b, ← heq b',h]
    · intro b j
      rw [eval_partialEval,heq]
      exact hz b.val j
    · intro b
      simpa only [q_483,eval_partialEval,heq] using hminor b.val
  calc
    Fintype.card β = ∑ x : ι → K, Fintype.card {b // free b = x} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv free)).symm
    _ ≤ ∑ _x : ι → K, (D+1)^Fintype.card κ := Finset.sum_le_sum (fun x _ => hfiber x)
    _ = Fintype.card K ^ Fintype.card ι * (D+1)^Fintype.card κ := by simp
noncomputable def q_1.goodResidues {n : ℕ} (P : q_1 n)
    (K : Type*) [Field K] [Fintype K] : Finset (Fin n → K) := by
  classical
  exact Finset.univ.filter fun x =>
    (∀ i, eval x (MvPolynomial.map (Int.castRingHom K) (P.equations i)) = 0) ∧
    eval x (MvPolynomial.map (Int.castRingHom K) P.minor) ≠ 0
theorem q_1.card_goodResidues {n : ℕ} (P : q_1 n)
    (K : Type*) [Field K] [Fintype K] (D : ℕ)
    (hD : ∀ i, (P.equations i).totalDegree ≤ D) :
    (P.goodResidues K).card ≤ Fintype.card K ^ Nat.card P.free * (D+1)^Nat.card ↥(P.freeᶜ) := by
  classical
  let e := Equiv.Set.sumCompl P.free
  let G : ↥(P.freeᶜ) → MvPolynomial (P.free ⊕ ↥(P.freeᶜ)) K :=
    fun i => rename e.symm (MvPolynomial.map (Int.castRingHom K) (P.equations i))
  let z : P.goodResidues K → (P.free ⊕ ↥(P.freeᶜ)) → K :=
    fun b j => b.val (e j)
  have hev (b : P.goodResidues K) (p : MvPolynomial (Fin n) K) :
      eval (z b) (rename e.symm p) = eval b.val p := by
    rw [eval_rename]
    simp [z,Function.comp_def]
  have heq (i : ↥(P.freeᶜ)) : e.symm i.val = Sum.inr i := by
    apply e.injective
    simp [e]
  have hcard := q_364 D G (fun i =>
    (totalDegree_rename_le e.symm _).trans
      ((Finset.sup_mono (support_map_subset _ _)).trans (hD i))) z
  have hz : Function.Injective z := by
    intro b c h
    apply Subtype.ext
    funext j
    simpa [z] using congrFun h (e.symm j)
  have hroot : ∀ b i, eval (z b) (G i) = 0 := by
    intro b i
    exact (hev b _).trans ((Finset.mem_filter.mp b.property).2.1 i)
  have hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0 := by
    intro b
    have heval : (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))) =
        (Matrix.of (fun i j => eval b.val (pderiv j.val
          (MvPolynomial.map (Int.castRingHom K) (P.equations i))))) := by
      ext i j
      change eval (z b) (pderiv (Sum.inr j) (rename e.symm _)) = _
      rw [← heq j,pderiv_rename e.symm.injective,hev]
      rfl
    rw [heval]
    have hb := (Finset.mem_filter.mp b.property).2.2
    rw [q_396] at hb
    have hd := (eval b.val).map_det (fun i j : ↥(P.freeᶜ) =>
      pderiv j.val (MvPolynomial.map (Int.castRingHom K) (P.equations i)))
    exact fun hz => hb (hd.trans hz)
  simpa only [Fintype.card_coe,Nat.card_eq_fintype_card] using hcard hz hroot hminor
open scoped Classical
def q_35 {n : ℕ} (Q : Finset ℕ) (z : Fin n → ℤ) :
    ∀ p : Q, Fin n → ZMod p.val := fun p i => (z i : ZMod p.val)
theorem q_94 {n : ℕ} (Q : Finset ℕ) (z w : Fin n → ℤ) :
    q_35 Q z = q_35 Q w ↔ ∀ p ∈ Q, ∀ i, (p : ℤ) ∣ w i-z i := by
  constructor
  · intro h p hp i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h ⟨p,hp⟩) i).symm
  · intro h
    funext p i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (w i-z i) p.val).mpr (h p.val p.property i)
    rw [Int.cast_sub,sub_eq_zero] at hz
    exact hz.symm
theorem q_1.eval_equation_zero {n : ℕ} {P : q_1 n}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.On I) {z : Fin n → ℤ}
    (hz : q_64 I z) (j : ↥(P.freeᶜ)) : eval z (P.equations j) = 0 := by
  have h := hz _ (hP.2.1 j)
  rw [q_218] at h
  exact_mod_cast h
theorem q_1.residue_mem_iff {n p : ℕ} (P : q_1 n) [Fact p.Prime]
    (z : Fin n → ℤ) (hz : ∀ j, eval z (P.equations j) = 0) :
    (fun i => (z i : ZMod p)) ∈ P.goodResidues (ZMod p) ↔ ¬ (p : ℤ) ∣ eval z P.minor := by
  classical
  simp only [q_1.goodResidues,Finset.mem_filter,Finset.mem_univ,true_and,q_218,hz,Int.cast_zero,implies_true,true_and]
  exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ p)
theorem q_433 {α : Type*} (Q : Finset α) (p : α → Prop) :
    (Finset.univ.filter fun a : Q => p a.val).card = (Q.filter p).card := by
  classical
  rw [Finset.card_filter,Finset.card_filter]
  exact Finset.sum_coe_sort Q (fun a => if p a then (1 : ℕ) else 0)
theorem q_1.card_bad_residue_tuple {n : ℕ} (P : q_1 n)
    (Q : Finset ℕ) [∀ p : Q, Fact p.val.Prime] (z : Fin n → ℤ)
    (hz : ∀ j, eval z (P.equations j) = 0) :
    (Finset.univ.filter fun p : Q => q_35 Q z p ∉ P.goodResidues (ZMod p.val)).card =
      (Q.filter fun p : ℕ => (p : ℤ) ∣ eval z P.minor).card := by
  classical
  have heq : (Finset.univ.filter fun p : Q => q_35 Q z p ∉ P.goodResidues (ZMod p.val)) =
      Finset.univ.filter fun p : Q => (p.val : ℤ) ∣ eval z P.minor := by
    apply Finset.filter_congr
    intro p _
    change ¬ ((fun i => (z i : ZMod p.val)) ∈ P.goodResidues (ZMod p.val)) ↔ _
    rw [P.residue_mem_iff z hz,not_not]
  rw [heq]
  convert q_433 Q (fun p : ℕ => (p : ℤ) ∣ eval z P.minor) using 1 <;> congr 1 <;> ext p <;> simp
theorem q_1.card_goodResidues_zmod_le {n p : ℕ} (P : q_1 n) [Fact p.Prime]
    (D h M : ℕ) (hM : 1 ≤ M) (hfree : Nat.card P.free ≤ h)
    (hD : ∀ j, (P.equations j).totalDegree ≤ D) (hupper : p ≤ M) :
    (P.goodResidues (ZMod p)).card ≤ (D+1)^n * M^h := by
  classical
  refine (P.card_goodResidues (ZMod p) D hD).trans ?_
  rw [ZMod.card]
  have hc : Nat.card ↥(P.freeᶜ) ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => i ∈ P.freeᶜ)
  calc
    p ^ Nat.card P.free * (D+1)^Nat.card ↥(P.freeᶜ) ≤ M^h*(D+1)^n := by
      apply Nat.mul_le_mul
      · exact (Nat.pow_le_pow_left hupper _).trans (Nat.pow_le_pow_right hM hfree)
      · exact Nat.pow_le_pow_right (by omega) hc
    _ = _ := by ring
theorem q_1.card_residue_image {n : ℕ} (P : q_1 n)
    (D h M b : ℕ) (hM : 1 ≤ M) (hfree : Nat.card P.free ≤ h)
    (hD : ∀ j, (P.equations j).totalDegree ≤ D)
    (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime) (hupper : ∀ p ∈ Q, p ≤ M)
    (S : Finset (Fin n → ℤ)) (hroot : ∀ z ∈ S, ∀ j, eval z (P.equations j) = 0)
    (hbad : ∀ z ∈ S, (Q.filter fun p : ℕ => (p : ℤ) ∣ eval z P.minor).card ≤ b) :
    (S.image (q_35 Q)).card ≤
      2^Q.card * ((D+1)^n)^Q.card * M^(h*Q.card+n*b) := by
  classical
  let (p : Q) : Fact p.val.Prime := ⟨hprime p.val p.property⟩
  let good (p : Q) : Finset (Fin n → ZMod p.val) := P.goodResidues (ZMod p.val)
  have hall (p : Q) : Fintype.card (Fin n → ZMod p.val) ≤ M^n := by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]
    exact Nat.pow_le_pow_left (hupper p.val p.property) n
  have hgood (p : Q) : (good p).card ≤ (D+1)^n * M^h :=
    P.card_goodResidues_zmod_le D h M hM hfree hD (hupper p.val p.property)
  let R : Finset (∀ p : Q, Fin n → ZMod p.val) := Finset.univ.filter fun x =>
    (Finset.univ.filter fun p => x p ∉ good p).card ≤ b
  have hsub : S.image (q_35 Q) ⊆ R := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (P.card_bad_residue_tuple Q z (hroot z hz)).le.trans (hbad z hz)
  exact (Finset.card_le_card hsub).trans (by
    simpa only [Fintype.card_coe] using
      q_306 good ((D+1)^n) M h n b (one_le_pow₀ (by omega)) hM hall hgood)
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
theorem q_117 {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (S : Finset α) (f : α → β) (g : α → γ) (L : ℕ)
    (hL : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).image g).card ≤ L) :
    (S.image g).card ≤ (S.image f).card * L := by
  classical
  have hsub : S.image g ⊆ (S.image f).biUnion fun b => (S.filter fun a => f a = b).image g := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_biUnion.mpr ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,rfl⟩⟩
  calc
    _ ≤ ((S.image f).biUnion fun b => (S.filter fun a => f a = b).image g).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ S.image f, ((S.filter fun a => f a = b).image g).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ S.image f, L := Finset.sum_le_sum hL
    _ = _ := by simp
noncomputable def q_65 {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) : ℕ → ℕ → σ → α → σ
  | 0, _, s, _ => s
  | m+1, i, s, a =>
    let t := q_65 W next m i s a
    next (i+m) t (W (i+m) t a)
theorem q_465 {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (m i : ℕ) (s : σ) (a : α) :
    q_65 W next m (i+1) (next i s (W i s a)) a =
      q_65 W next (m+1) i s a := by
  induction m with
  | zero => simp [q_65]
  | succ m ih =>
    simp only [q_65,ih]
    rw [show i+1+m = i+(m+1) by omega]
theorem q_349 {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (m j i : ℕ) (s : σ) (a : α)
    (hj : j ≤ m) : q_65 W next j i s a ∈ q_17 W next m i s a := by
  induction m generalizing j i s with
  | zero =>
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp [q_65,q_17]
  | succ m ih =>
    cases j with
    | zero => simp [q_65,q_17]
    | succ j =>
      rw [← q_465]
      exact List.mem_cons_of_mem _ (ih j (i+1) _ (by omega))
noncomputable def q_2 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    Ideal (MvPolynomial (Fin n) ℂ) × q_1 n :=
  q_65 (q_22 (E := E) G d z.val) (q_81 G d A h e z.val) i 0 (start z) B
theorem q_89 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    q_2 (E := E) G d A h e start B (i+1) z =
      q_81 G d A h e z.val i (q_2 (E := E) G d A h e start B i z)
        (q_22 (E := E) G d z.val i (q_2 (E := E) G d A h e start B i z) B) := by
  simp only [q_2,q_65,Nat.zero_add]
theorem q_30 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    q_29 G h (q_4 n d A h e i) z.val
      (q_2 (E := E) G d A h e start B i z) := by
  induction i with
  | zero => exact hs z
  | succ i ih =>
    rw [q_89]
    exact (q_171 (E := E) G d A h e z.val z.property i _ ih B).1
noncomputable def q_33 {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun j => j.val < i).biUnion B
@[simp] theorem pastBlockPrimes_zero {r : ℕ} (B : Fin r → Finset ℕ) :
    q_33 B 0 = ∅ := by simp [q_33]
theorem q_459 {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) :
    q_33 B (i+1) = q_9 B i := by
  simp only [q_33,q_9,Nat.lt_succ_iff]
theorem q_245 {r : ℕ} (B : Fin r → Finset ℕ) (i : Fin r) :
    q_9 B i.val = q_33 B i.val ∪ B i := by
  classical
  ext p
  simp only [q_9,q_33,Finset.mem_biUnion,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨j,hj,hp⟩
    rcases lt_or_eq_of_le hj with hj | hj
    · exact Or.inl ⟨j,hj,hp⟩
    · have he : j = i := Fin.ext hj
      subst j
      exact Or.inr hp
  · rintro (⟨j,hj,hp⟩ | hp)
    · exact ⟨j,hj.le,hp⟩
    · exact ⟨i,le_rfl,hp⟩
theorem q_320 {n r : ℕ} (B : Fin r → Finset ℕ) (i : Fin r)
    (z w : Fin n → ℤ) (hprev : q_35 (q_33 B i.val) z = q_35 (q_33 B i.val) w)
    (hnew : q_35 (B i) z = q_35 (B i) w) :
    q_35 (q_9 B i.val) z = q_35 (q_9 B i.val) w := by
  apply (q_94 _ _ _).mpr
  intro p hp j
  rw [q_245] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (q_94 _ _ _).mp hprev p hp j
  · exact (q_94 _ _ _).mp hnew p hp j
noncomputable def q_41 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n) ×
      (∀ p : q_33 B i, Fin n → ZMod p.val) :=
  (q_2 (E := E) G d A h e start B i z, q_35 (q_33 B i) z.val)
theorem q_225 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points)
    (hstate : ∀ w ∈ S, q_2 (E := E) G d A h e start B i w =
      q_2 (E := E) G d A h e start B i z)
    (hres : ∀ w ∈ S, q_35 (q_9 B i) w.val =
      q_35 (q_9 B i) z.val) :
    (S.image (q_41 (E := E) G d A h e start B (i+1))).card ≤
      q_27 (d i) h (q_4 n d A h e i) *
        q_19 n A h (q_12 (d i) h (q_4 n d A h e i)) := by
  classical
  let s := q_2 (E := E) G d A h e start B i z
  let W := q_22 (E := E) G d z.val i s B
  let L := q_86 G (d i) A h (q_4 n d A h e i) s.1 W
  have hz := q_30 (E := E) G d A h e start hs B i z
  have hL := q_168 G (d i) A h (q_4 n d A h e i) s.1 W hz.1
  let f := fun t : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n =>
    (t, q_35 (q_33 B (i+1)) z.val)
  have hsub : S.image (q_41 (E := E) G d A h e start B (i+1)) ⊆ L.toFinset.image f := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hsw := q_30 (E := E) G d A h e start hs B i w
    have hstep := q_171 (E := E) G d A h e w.val w.property i _ hsw B
    have hkernel : q_22 (E := E) G d w.val i s B = W := by
      unfold W q_22
      congr 1
      exact q_244 _ _ _ _ _ ((q_94 _ _ _).mp (hres w hw))
    have hm : q_2 (E := E) G d A h e start B (i+1) w ∈ L := by
      rw [q_89]
      have hm := hstep.2.1
      rw [hstate w hw] at hm ⊢
      change q_81 G d A h e w.val i s (q_22 (E := E) G d w.val i s B) ∈ L
      change q_81 G d A h e w.val i s (q_22 (E := E) G d w.val i s B) ∈
        q_86 G (d i) A h (q_4 n d A h e i) s.1 (q_22 (E := E) G d w.val i s B) at hm
      rw [hkernel] at hm ⊢
      exact hm
    refine Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr hm,?_⟩
    apply Prod.ext
    · rfl
    · change q_35 (q_33 B (i+1)) z.val = q_35 (q_33 B (i+1)) w.val
      rw [q_459]
      exact (hres w hw).symm
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans
    ((List.toFinset_card_le L).trans hL.1))
end
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
theorem q_326 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : Fin r) (z : G.points) (S : Finset G.points)
    (hnode : ∀ w ∈ S, q_41 (E := E) G d A h e start B i.val w =
      q_41 (E := E) G d A h e start B i.val z)
    (q M b : ℕ) (hM : 1 ≤ M)
    (hdim : q_0 (q_2 (E := E) G d A h e start B i.val z).1 ≤ q)
    (hprime : ∀ p ∈ B i, p.Prime) (hupper : ∀ p ∈ B i, p ≤ M)
    (hbad : ∀ w ∈ S, ((B i).filter fun p : ℕ => (p : ℤ) ∣
      eval w.val (q_2 (E := E) G d A h e start B i.val w).2.minor).card ≤ b) :
    (S.image (q_41 (E := E) G d A h e start B (i.val+1))).card ≤
      (2^(B i).card * ((q_4 n d A h e i.val+1)^n)^(B i).card *
        M^(q*(B i).card+n*b)) *
      (q_27 (d i.val) h (q_4 n d A h e i.val) *
        q_19 n A h (q_12 (d i.val) h (q_4 n d A h e i.val))) := by
  classical
  let P := (q_2 (E := E) G d A h e start B i.val z).2
  let s := q_2 (E := E) G d A h e start B i.val z
  have hg := q_30 (E := E) G d A h e start hs B i.val z
  have hstate (w : G.points) (hw : w ∈ S) :
      q_2 (E := E) G d A h e start B i.val w = s :=
    congrArg Prod.fst (hnode w hw)
  have hprev (w : G.points) (hw : w ∈ S) :
      q_35 (q_33 B i.val) w.val = q_35 (q_33 B i.val) z.val :=
    congrArg Prod.snd (hnode w hw)
  let label : G.points → ∀ p : B i, Fin n → ZMod p.val := fun w => q_35 (B i) w.val
  let K := q_27 (d i.val) h (q_4 n d A h e i.val) *
        q_19 n A h (q_12 (d i.val) h (q_4 n d A h e i.val))
  have hfib (a) (ha : a ∈ S.image label) :
      ((S.filter fun w => label w = a).image (q_41 (E := E) G d A h e start B (i.val+1))).card ≤ K := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    apply q_225 G d A h e start hs B i.val v
    · intro w hw
      obtain ⟨hw,_⟩ := Finset.mem_filter.mp hw
      exact (hstate w hw).trans (hstate v hv).symm
    · intro w hw
      obtain ⟨hw,hr⟩ := Finset.mem_filter.mp hw
      exact q_320 B i w.val v.val
        ((hprev w hw).trans (hprev v hv).symm) hr
  have hres : (S.image label).card ≤
      2^(B i).card * ((q_4 n d A h e i.val+1)^n)^(B i).card * M^(q*(B i).card+n*b) := by
    let Z := S.image (fun w => w.val)
    have hfree : Nat.card P.free ≤ q := hg.2.1.1.trans_le hdim
    have hD : ∀ j, (P.equations j).totalDegree ≤ q_4 n d A h e i.val := by
      obtain ⟨dd,hdd,hd,_⟩ := hg.2.2.1
      exact fun j => (hd j).trans hdd
    have hroot : ∀ w ∈ Z, ∀ j, eval w (P.equations j) = 0 := by
      rintro w hw j
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hgv := q_30 (E := E) G d A h e start hs B i.val v
      rw [hstate v hv] at hgv
      exact q_1.eval_equation_zero hgv.2.1 hgv.2.2.2.1 j
    have hb : ∀ w ∈ Z, ((B i).filter fun p : ℕ => (p : ℤ) ∣ eval w P.minor).card ≤ b := by
      rintro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hvb := hbad v hv
      rw [hstate v hv] at hvb
      exact hvb
    have hc := P.card_residue_image (q_4 n d A h e i.val) q M b hM hfree hD
      (B i) hprime hupper Z hroot hb
    simpa only [Z,Finset.image_image,Function.comp_def,label] using hc
  exact (q_117 S label _ K hfib).trans (Nat.mul_le_mul_right K hres)
end
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
noncomputable def q_53 {α : Type*} (S : Finset α) (stop : α → ℕ) (i : ℕ) : Finset α :=
  S.filter fun z => i ≤ stop z
theorem q_394 {α : Type*} (S : Finset α) (stop : α → ℕ) (i : ℕ) :
    q_53 S stop (i+1) ⊆ q_53 S stop i := by
  intro z hz
  obtain ⟨hz,hi⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz,by omega⟩
theorem q_498 {α : Type*} {β : ℕ → Type*} [∀ i, DecidableEq (β i)] (S : Finset α)
    (stop : α → ℕ) (node : (i : ℕ) → α → β i) (B : ℕ → ℕ) (r C : ℕ)
    (hzero : ((q_53 S stop 0).image (node 0)).card ≤ C)
    (hchild : ∀ i < r, ∀ a ∈ (q_53 S stop (i+1)).image (node i),
      (((q_53 S stop (i+1)).filter fun z => node i z = a).image (node (i+1))).card ≤ B i) :
    ∀ i ≤ r, ((q_53 S stop i).image (node i)).card ≤ C*∏ j ∈ Finset.range i, B j := by
  intro i hi
  induction i with
  | zero => simpa using hzero
  | succ i ih =>
    have hcount := q_117 (q_53 S stop (i+1)) (node i) (node (i+1)) (B i)
      (hchild i (by omega))
    have hsub := Finset.card_le_card (Finset.image_subset_image (f := node i) (q_394 S stop i))
    calc
      _ ≤ ((q_53 S stop (i+1)).image (node i)).card * B i := hcount
      _ ≤ ((q_53 S stop i).image (node i)).card * B i := Nat.mul_le_mul_right _ hsub
      _ ≤ (C * ∏ j ∈ Finset.range i, B j) * B i := Nat.mul_le_mul_right _ (ih (by omega))
      _ = _ := by rw [Finset.prod_range_succ,mul_assoc]
theorem q_454 {α : Type*} {β : ℕ → Type*} [∀ i, DecidableEq (β i)] (S : Finset α)
    (stop : α → ℕ) (node : (i : ℕ) → α → β i) (B : ℕ → ℕ) (r L : ℕ)
    (hstop : ∀ z ∈ S, stop z ≤ r)
    (hnodes : ∀ i ≤ r, ((q_53 S stop i).image (node i)).card ≤ B i)
    (hterminal : ∀ i ≤ r, ∀ a ∈ (q_53 S stop i).image (node i),
      (S.filter fun z => stop z = i ∧ node i z = a).card ≤ L) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), B i)*L := by
  classical
  have hs (i : ℕ) (hi : i ≤ r) : (S.filter fun z => stop z = i).card ≤ B i * L := by
    let T := S.filter fun z => stop z = i
    have hsub : T ⊆ q_53 S stop i := by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz,he.ge⟩
    have hf (a) (ha : a ∈ T.image (node i)) :
        ((T.filter fun z => node i z = a).image id).card ≤ L := by
      have ha' : a ∈ (q_53 S stop i).image (node i) := Finset.image_subset_image hsub ha
      simpa only [Finset.image_id,Finset.filter_filter,T] using hterminal i hi a ha'
    have hh := q_117 T (node i) id L hf
    rw [Finset.image_id] at hh
    exact hh.trans (Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.image_subset_image hsub)).trans (hnodes i hi)))
  calc
    S.card = ∑ i ∈ Finset.range (r+1), (S.filter fun z => stop z = i).card :=
      Finset.card_eq_sum_card_fiberwise (fun z hz => Finset.mem_range.mpr (by have := hstop z hz; omega))
    _ ≤ ∑ i ∈ Finset.range (r+1), B i * L := Finset.sum_le_sum (fun i hi => hs i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := (Finset.sum_mul _ _ _).symm
theorem q_299 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (S : Finset G.points)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n))
    (hs : ∀ z ∈ S, start z ∈ L) :
    (S.image (q_41 (E := E) G d A h e start B 0)).card ≤ L.length := by
  classical
  let f := fun t : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n =>
    (t,q_35 (q_33 B 0) (fun _ : Fin n => 0))
  have hsub : S.image (q_41 (E := E) G d A h e start B 0) ⊆ L.toFinset.image f := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨start z,List.mem_toFinset.mpr (hs z hz),?_⟩
    apply Prod.ext
    · rfl
    · apply (q_94 _ _ _).mpr
      simp
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (List.toFinset_card_le L))
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
noncomputable def q_31 {r : ℕ} (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ)
    (B : Fin r → Finset ℕ) (M b q : Fin r → ℕ) (i : Fin r) : ℕ :=
  (2^(B i).card * ((q_4 n d A h e i.val+1)^n)^(B i).card *
    M i ^ (q i*(B i).card+n*b i)) *
  (q_27 (d i.val) h (q_4 n d A h e i.val) *
    q_19 n A h (q_12 (d i.val) h (q_4 n d A h e i.val)))
theorem q_442 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (stop : G.points → ℕ) (M b q : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)) (T : ℕ)
    (hstart : ∀ z ∈ S, start z ∈ L) (hstop : ∀ z ∈ S, stop z ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hdim : ∀ i : Fin r, ∀ z ∈ S, i.val < stop z →
      q_0 (q_2 (E := E) G d A h e start B i.val z).1 ≤ q i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S, i.val < stop z →
      ((B i).filter fun p : ℕ => (p : ℤ) ∣ eval z.val
        (q_2 (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hterminal : ∀ i ≤ r, ∀ z ∈ S, stop z = i →
      (S.filter fun w => stop w = i ∧ q_41 (E := E) G d A h e start B i w =
        q_41 (E := E) G d A h e start B i z).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1),
      L.length * ∏ j ∈ Finset.range i,
        if hj : j < r then q_31 n d A h e B M b q ⟨j,hj⟩ else 1) * T := by
  classical
  let node := q_41 (E := E) G d A h e start B
  let C := fun j : ℕ => if hj : j < r then q_31 n d A h e B M b q ⟨j,hj⟩ else 1
  have hzero : ((q_53 S stop 0).image (node 0)).card ≤ L.length := by
    apply q_299 G d A h e start B _ L
    intro z hz
    exact hstart z (Finset.mem_filter.mp hz).1
  have hchild : ∀ j < r, ∀ a ∈ (q_53 S stop (j+1)).image (node j),
      (((q_53 S stop (j+1)).filter fun z => node j z = a).image (node (j+1))).card ≤ C j := by
    intro j hj a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hjstop⟩ := Finset.mem_filter.mp hz
    have hcount := q_326 G d A h e start hs B ⟨j,hj⟩ z
      ((q_53 S stop (j+1)).filter fun z' => node j z' = node j z)
      (fun w hw => (Finset.mem_filter.mp hw).2) (q ⟨j,hj⟩) (M ⟨j,hj⟩) (b ⟨j,hj⟩)
      (hM ⟨j,hj⟩) (hdim ⟨j,hj⟩ z hz (by change j < stop z; omega)) (hprime ⟨j,hj⟩) (hupper ⟨j,hj⟩)
      (fun w hw => hbad ⟨j,hj⟩ w (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
        (by change j < stop w; have := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2; omega))
    simpa only [C,dif_pos hj,q_31] using hcount
  have hnodes := q_498 S stop node C r L.length hzero hchild
  apply q_454 S stop node (fun i => L.length*∏ j ∈ Finset.range i, C j) r T hstop hnodes
  intro i hi a ha
  by_cases he : ∃ z ∈ S, stop z = i ∧ node i z = a
  · obtain ⟨z,hz,hzi,rfl⟩ := he
    convert hterminal i hi z hz hzi using 1
  · have hempty : (S.filter fun z => stop z = i ∧ node i z = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact he ⟨z,(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩
    have hh := Finset.card_eq_zero.mpr hempty
    apply (show _ = 0 by convert hh using 1).le.trans
    exact Nat.zero_le _
end
open MvPolynomial
open scoped BigOperators
theorem q_323 {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : R) (w : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i j, q ^ w i ∣ A i j) : q ^ (∑ i, w i) ∣ A.det := by
  choose B hB using hA
  have hmatrix : A = Matrix.of (fun i j => q ^ w i * B i j) := by
    ext i j
    exact hB i j
  rw [hmatrix]
  change q ^ (∑ i, w i) ∣ (Matrix.of (fun i j => q ^ w i * (Matrix.of B) i j)).det
  rw [Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _
theorem q_195
    {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (q : R) (m : ℕ) (w : τ → ℕ)
    (v : τ → ι → R) (c : ι → τ → R)
    (hv : ∀ a j, q ^ w a ∣ v a j)
    (hm : ∀ r : ι → τ, Function.Injective r → m ≤ ∑ i, w (r i)) :
    q ^ m ∣ (Matrix.of (fun i j => ∑ a, c i a * v a j)).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  have hexpand : (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
    change L (fun i j => ∑ a, c i a * v a j) =
      ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
    have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
    simp only [AlternatingMap.coe_multilinearMap] at h
    have hfun : (fun i => ∑ a, c i a • v a) =
        (fun i j => ∑ a, c i a * v a j) := by
      funext i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun] at h
    simpa only [AlternatingMap.map_smul_univ, smul_eq_mul] using h
  rw [hexpand]
  apply Finset.dvd_sum
  intro r _
  by_cases hr : Function.Injective r
  · apply dvd_mul_of_dvd_right
    exact (pow_dvd_pow q (hm r hr)).trans
      (q_323 q (fun i => w (r i)) _ (fun i j => hv (r i) j))
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hr
    have hz : (Matrix.of (fun i => v (r i))).det = 0 := by
      exact L.map_eq_zero_of_eq (fun i => v (r i)) (congrArg v hab) hne
    rw [hz, mul_zero]
    exact dvd_zero _
theorem q_229 {σ ι R : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] (q : R) (m : ℕ)
    (P : ι → MvPolynomial σ R) (x : ι → σ → R)
    (hx : ∀ j a, q ∣ x j a)
    (hm : ∀ r : ι → (σ →₀ ℕ), Function.Injective r →
      m ≤ ∑ i, (r i).sum (fun _ e => e)) :
    q ^ m ∣ (Matrix.of (fun i j => eval (x j) (P i))).det := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion (fun i => (P i).support)
  let v : s → ι → R := fun a j => a.val.prod (fun l e => x j l ^ e)
  let c : ι → s → R := fun i a => (P i).coeff a.val
  have hv : ∀ a j, q ^ a.val.sum (fun _ e => e) ∣ v a j := by
    intro a j
    dsimp [v, Finsupp.sum, Finsupp.prod]
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun l _ => pow_dvd_pow_of_dvd (hx j l) _)
  have hweight : ∀ r : ι → s, Function.Injective r →
      m ≤ ∑ i, (r i).val.sum (fun _ e => e) := by
    intro r hr
    exact hm (fun i => (r i).val) (Subtype.val_injective.comp hr)
  have heq : (Matrix.of (fun i j => eval (x j) (P i))) =
      Matrix.of (fun i j => ∑ a : s, c i a * v a j) := by
    ext i j
    simp only [Matrix.of_apply, c, v, Finsupp.prod, eval_eq]
    rw [Finset.sum_coe_sort s (fun a => (P i).coeff a * ∏ l ∈ a.support, x j l ^ a l)]
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩
    · intro a _ ha
      have hz : (P i).coeff a = 0 := by
        simpa only [MvPolynomial.mem_support_iff, not_not] using ha
      simp only [hz, zero_mul]
  rw [heq]
  exact q_195 q m (fun a : s => a.val.sum (fun _ e => e))
    v c hv hweight
theorem q_259 {ι κ α R : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] [CommRing R]
    (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (q_20 G).det)
    (q : R) (m : ℕ) (hqm : q ^ m = 0)
    (P : α → MvPolynomial (ι ⊕ κ) R) (x : α → ι → R) (y : α → κ → R)
    (hx : ∀ a i, q ∣ x a i) (hy : ∀ a j, q ∣ y a j)
    (hroot : ∀ a j, eval (Sum.elim (x a) (y a)) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))).det = 0 := by
  obtain ⟨F, _, hF⟩ := q_238 G hzero hunit q m
  have heval : ∀ a j, y a j = eval (x a) (F j) := by
    intro a j
    have h := hF (x a) (y a) (hx a) (hy a) (hroot a) j
    simpa only [pow_succ, hqm, zero_mul, zero_dvd_iff, sub_eq_zero] using h
  let Q : α → MvPolynomial ι R := fun a => eval₂ C (Sum.elim X F) (P a)
  have heq : (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))) =
      Matrix.of (fun a b => eval (x b) (Q a)) := by
    ext a b
    dsimp only [Q, Matrix.of_apply]
    rw [q_213]
    congr 2
    funext c
    cases c with
    | inl c => simp
    | inr c => exact heval b c
  rw [heq]
  have h := q_229 q m Q x hx hm
  simpa only [hqm, zero_dvd_iff] using h
theorem q_375 {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : MvPolynomial σ R) (x : σ → R) :
    eval (fun i => φ (x i)) (map φ P) = φ (eval x P) := by
  rw [eval_map, eval₂_comp]
  rfl
theorem q_335 {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ m)) := by
  have hn : ¬ p ∣ a.natAbs := by simpa only [← Int.natCast_dvd] using ha
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hm).mpr hn
  have hu' : IsUnit (((a.natAbs : ℕ) : ℤ) : ZMod (p ^ m)) := by
    simpa only [Int.cast_natCast] using hu
  rw [Int.natCast_natAbs] at hu'
  rcases le_total 0 a with hpos | hneg
  · rwa [abs_of_nonneg hpos] at hu'
  · rw [abs_of_nonpos hneg, Int.cast_neg] at hu'
    simpa only [neg_neg] using hu'.neg
theorem q_276 {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ (p : ℤ) ∣ (q_20 G).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ)
    (x : α → ι → ℤ) (y : α → κ → ℤ)
    (hx : ∀ a i, (p : ℤ) ∣ x a i) (hy : ∀ a j, (p : ℤ) ∣ y a j)
    (hroot : ∀ a j, eval (Sum.elim (x a) (y a)) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (p : ℤ) ^ m ∣
      (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))).det := by
  classical
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  let R := ZMod (p ^ m)
  let φ : ℤ →+* R := Int.castRingHom R
  let G' : κ → MvPolynomial (ι ⊕ κ) R := fun j => map φ (G j)
  let P' : α → MvPolynomial (ι ⊕ κ) R := fun a => map φ (P a)
  let x' : α → ι → R := fun a i => φ (x a i)
  let y' : α → κ → R := fun a j => φ (y a j)
  have hzero' : ∀ j, eval (fun _ => 0) (G' j) = 0 := by
    intro j
    have h := q_375 φ (G j) (fun _ => 0)
    simpa only [G', map_zero, hzero] using h
  have hjac : q_20 G' = φ.mapMatrix (q_20 G) := by
    ext j a
    change eval (fun _ => 0) (pderiv (Sum.inr a) (map φ (G j))) =
      φ (eval (fun _ => 0) (pderiv (Sum.inr a) (G j)))
    rw [pderiv_map]
    simpa only [map_zero] using q_375 φ (pderiv (Sum.inr a) (G j)) (fun _ => 0)
  have hunit : IsUnit (q_20 G').det := by
    rw [hjac, ← φ.map_det]
    exact q_335 hp hmpos _ hgood
  have hqm : (φ (p : ℤ)) ^ m = 0 := by
    change (((p : ℕ) : ℤ) : ZMod (p ^ m)) ^ m = 0
    rw [Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have hx' : ∀ a i, φ (p : ℤ) ∣ x' a i := fun a i => map_dvd φ (hx a i)
  have hy' : ∀ a j, φ (p : ℤ) ∣ y' a j := fun a j => map_dvd φ (hy a j)
  have heval (a : α) (T : MvPolynomial (ι ⊕ κ) ℤ) :
      eval (Sum.elim (x' a) (y' a)) (map φ T) =
        φ (eval (Sum.elim (x a) (y a)) T) := by
    have hf : (fun i => φ ((Sum.elim (x a) (y a)) i)) = Sum.elim (x' a) (y' a) := by
      funext i
      cases i <;> rfl
    rw [← hf]
    exact q_375 φ T _
  have hroot' : ∀ a j, eval (Sum.elim (x' a) (y' a)) (G' j) = 0 := by
    intro a j
    rw [show G' j = map φ (G j) from rfl, heval, hroot, map_zero]
  have hdet := q_259 G' hzero' hunit (φ (p : ℤ)) m hqm
    P' x' y' hx' hy' hroot' hm
  let A : Matrix α α ℤ := Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))
  have hA : φ.mapMatrix A = Matrix.of (fun a b => eval (Sum.elim (x' b) (y' b)) (P' a)) := by
    ext a b
    exact (heval b (P a)).symm
  have hz : (A.det : ZMod (p ^ m)) = 0 := by
    change φ A.det = 0
    rw [φ.map_det, hA]
    exact hdet
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd A.det (p ^ m)).mp hz
  simpa only [Nat.cast_pow] using hd
noncomputable def q_55 {σ R : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  eval₂ C (fun i => X i + C (z i)) P
theorem q_192 {σ R : Type*} [CommRing R]
    (z x : σ → R) (P : MvPolynomial σ R) :
    eval x (q_55 z P) = eval (fun i => x i + z i) P := by
  rw [q_55, q_213]
  simp only [map_add, eval_X, eval_C]
theorem q_444 {σ R : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) (i : σ) :
    pderiv i (q_55 z P) = q_55 z (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [q_55]
  | add P Q hP hQ => simpa only [q_55, eval₂_add, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
    by_cases h : i = j
    · subst j
      simpa only [q_55, eval₂_mul, eval₂_X, pderiv_mul, map_add, pderiv_X,
        Pi.single_eq_same, pderiv_C, add_zero, mul_one, eval₂_add, eval₂_one, eval₂_zero,
        mul_zero, add_zero] using congrArg (fun T => T * (X i + C (z i)) +
          q_55 z P) hP
    · have h' : j ≠ i := Ne.symm h
      simpa only [q_55, eval₂_mul, eval₂_X, pderiv_mul, map_add, pderiv_X,
        Pi.single_eq_of_ne h', pderiv_C, add_zero, mul_zero, eval₂_add, eval₂_one,
        eval₂_zero, mul_zero, add_zero] using congrArg (fun T => T * (X j + C (z j))) hP
theorem q_237 {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0)
    {p : ℕ} (hp : p.Prime)
    (hgood : ¬ (p : ℤ) ∣ (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (p : ℤ) ^ m ∣ (Matrix.of (fun a b => eval (w b) (P a))).det := by
  let G' : κ → MvPolynomial (ι ⊕ κ) ℤ := fun j => q_55 z (G j)
  let P' : α → MvPolynomial (ι ⊕ κ) ℤ := fun a => q_55 z (P a)
  let x : α → ι → ℤ := fun a i => w a (Sum.inl i) - z (Sum.inl i)
  let y : α → κ → ℤ := fun a j => w a (Sum.inr j) - z (Sum.inr j)
  have hzero : ∀ j, eval (fun _ => 0) (G' j) = 0 := by
    intro j
    simpa only [G', q_192, zero_add] using hz j
  have hjac : q_20 G' =
      Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j))) := by
    ext j a
    simp only [q_20, Matrix.of_apply, G', q_444,
      q_192, zero_add]
  have hgood' : ¬ (p : ℤ) ∣ (q_20 G').det := by rwa [hjac]
  have hs (a : α) (T : MvPolynomial (ι ⊕ κ) ℤ) :
      eval (Sum.elim (x a) (y a)) (q_55 z T) = eval (w a) T := by
    rw [q_192]
    congr 2
    funext i
    cases i <;> simp [x, y]
  have hx : ∀ a i, (p : ℤ) ∣ x a i := fun a i => hw a (Sum.inl i)
  have hy : ∀ a j, (p : ℤ) ∣ y a j := fun a j => hw a (Sum.inr j)
  have hroot' : ∀ a j, eval (Sum.elim (x a) (y a)) (G' j) = 0 := by
    intro a j
    rw [show G' j = q_55 z (G j) from rfl, hs, hroot]
  have h := q_276 G' hzero hp hgood' m P' x y hx hy hroot' hm
  have heq : (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P' a))) =
      Matrix.of (fun a b => eval (w b) (P a)) := by
    ext a b
    exact hs b (P a)
  rwa [heq] at h
theorem q_317 {α : Type*} (s : Finset α) (f : α → ℕ) (t : ℕ) :
    ∑ a ∈ s, min (f a) t = ∑ j ∈ Finset.range t, (s.filter (fun a => j < f a)).card := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> omega
theorem q_331 {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → (ι →₀ ℕ)) (hr : Function.Injective r) (t : ℕ) :
    t * Fintype.card α ≤ (∑ a, q_38 (r a)) +
      ∑ j ∈ Finset.range t, (j + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  have hcard (j : ℕ) : (Finset.univ.filter (fun a => q_38 (r a) ≤ j)).card ≤
      (j + Fintype.card ι).choose (Fintype.card ι) := by
    rw [← q_220 ι j]
    exact Finset.card_le_card_of_injOn r
      (fun a ha => q_120.mpr (Finset.mem_filter.mp ha).2)
      (fun _ _ _ _ h => hr h)
  have hsum : t * Fintype.card α ≤
      (∑ a, q_38 (r a)) +
        ∑ j ∈ Finset.range t, (Finset.univ.filter (fun a => q_38 (r a) ≤ j)).card := by
    have hmin := q_317 Finset.univ (fun a => q_38 (r a)) t
    have hcompl (j : ℕ) :
        (Finset.univ.filter (fun a => j < q_38 (r a))).card +
        (Finset.univ.filter (fun a => q_38 (r a) ≤ j)).card = Fintype.card α := by
      simpa only [not_lt, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a => j < q_38 (r a))
    have heq : (∑ a, min (q_38 (r a)) t) +
        ∑ j ∈ Finset.range t, (Finset.univ.filter (fun a => q_38 (r a) ≤ j)).card =
        t * Fintype.card α := by
      rw [hmin, ← Finset.sum_add_distrib]
      simp_rw [hcompl]
      simp
    rw [← heq]
    exact Nat.add_le_add_right (Finset.sum_le_sum (fun a _ => min_le_left _ _)) _
  exact hsum.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => hcard j)) _)
theorem q_499 (h t : ℕ) :
    (∑ j ∈ Finset.range t, (j + h).choose h) = (t + h).choose (h + 1) := by
  cases t with
  | zero => simp
  | succ t => simpa only [Nat.succ_eq_add_one, Nat.add_right_comm t 1 h]
      using Nat.sum_range_add_choose t h
theorem q_288 {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → (ι →₀ ℕ)) (hr : Function.Injective r) (t : ℕ)
    (hcard : (t + Fintype.card ι).choose (Fintype.card ι) ≤ Fintype.card α) :
    Fintype.card ι * (t + Fintype.card ι).choose (Fintype.card ι + 1) ≤
      ∑ a, q_38 (r a) := by
  have h := q_331 r hr t
  rw [q_499] at h
  have heq := Nat.choose_succ_right_eq (t + Fintype.card ι) (Fintype.card ι)
  rw [Nat.add_sub_cancel_right] at heq
  have hmul := Nat.mul_le_mul_left t hcard
  nlinarith
open Matrix
theorem q_507 {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (v : τ → ι → R) (c : ι → τ → R) :
    (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  change L (fun i j => ∑ a, c i a * v a j) =
    ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
  have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
  simp only [AlternatingMap.coe_multilinearMap] at h
  have hfun : (fun i => ∑ a, c i a • v a) =
      (fun i j => ∑ a, c i a * v a j) := by
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun] at h
  simpa only [AlternatingMap.map_smul_univ, smul_eq_mul] using h
theorem q_203 {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (v : ι → α → ℚ)
    (hdet : ∀ r : ι → α, (Matrix.of (fun i j => v i (r j))).det = 0) :
    ∃ c : ι → ℚ, c ≠ 0 ∧ ∀ a, ∑ i, c i * v i a = 0 := by
  classical
  let A : Matrix ι α ℚ := Matrix.of v
  have hgram : (A * A.transpose).det = 0 := by
    change (Matrix.of (fun i j => ∑ a, v i a * v j a)).det = 0
    rw [q_507 (fun a j => v j a) v]
    apply Finset.sum_eq_zero
    intro r _
    have hr : (Matrix.of (fun i j => v j (r i))).det = 0 := by
      change ((Matrix.of (fun i j => v i (r j))).transpose).det = 0
      rw [Matrix.det_transpose, hdet r]
    rw [hr, mul_zero]
  obtain ⟨c, hc, hzc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hgram
  refine ⟨c, hc, ?_⟩
  have hzero : A.transpose *ᵥ c = 0 := by
    rw [← Matrix.mulVec_mulVec] at hzc
    have h := congrArg (fun v => dotProduct c v) hzc
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at h
    exact h
  intro a
  have h := congrFun hzero a
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
    A, Matrix.of_apply, mul_comm] using h
open Matrix
theorem q_165 {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (∏ p ∈ Q, (p : ℤ)) ^ m ∣ (Matrix.of (fun a b => eval (w b) (P a))).det := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_nat_coprime]
    simpa only [Int.natAbs_natCast] using (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  · intro p hp
    exact q_237 G z hz (hprime p hp) (hgood p hp) m P w
      (hw p hp) hroot hm
theorem q_152 {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (P a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p : ℝ)) ^ m) :
    (Matrix.of (fun a b => eval (w b) (P a))).det = 0 := by
  let A : Matrix α α ℤ := Matrix.of (fun a b => eval (w b) (P a))
  have hdiv : (∏ p ∈ Q, (p : ℤ)) ^ m ∣ A.det :=
    q_165 G z hz Q hprime hgood m P w hw hroot hm
  apply Int.eq_zero_of_abs_lt_dvd hdiv
  have hB' := q_99 ((Int.castRingHom ℝ).mapMatrix A) B hB
  rw [← (Int.castRingHom ℝ).map_det] at hB'
  change |(A.det : ℝ)| ≤ _ at hB'
  have h := hB'.trans_lt hlt
  apply (Int.cast_lt (R := ℝ)).mp
  simpa only [Int.cast_abs, Int.cast_pow, Int.cast_prod, Int.cast_natCast] using h
theorem q_260 {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : β → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (P a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p : ℝ)) ^ m) :
    ∃ c : α → ℚ, c ≠ 0 ∧ ∀ b, ∑ a, c a * (eval (w b) (P a) : ℚ) = 0 := by
  apply q_203
  intro r
  have hzero := q_152 G z hz Q hprime hgood m P
    (fun a => w (r a)) (fun p hp a i => hw p hp (r a) i)
    (fun a j => hroot (r a) j) hm B (fun a b => hB a (r b)) hlt
  have h := congrArg (Int.castRingHom ℚ) hzero
  rw [(Int.castRingHom ℚ).map_det, map_zero] at h
  exact h
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open scoped BigOperators
theorem q_174 {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (S A : Finset ι)
    (hAS : A ⊆ S) (hA : LinearIndepOn K v (A : Set ι)) (m : ℕ)
    (hAm : A.card ≤ m) (hm : m ≤ Module.finrank K (Submodule.span K (v '' (S : Set ι)))) :
    ∃ B : Finset ι, A ⊆ B ∧ B ⊆ S ∧ B.card = m ∧ LinearIndepOn K v (B : Set ι) := by
  classical
  have hsub : (A : Set ι) ⊆ (S : Set ι) := hAS
  let T := hA.extend hsub
  have hTs : T ⊆ (S : Set ι) := hA.extend_subset hsub
  have hfin : T.Finite := S.finite_toSet.subset hTs
  let B := hfin.toFinset
  have hli : LinearIndepOn K v (B : Set ι) := by
    simpa only [B, Set.Finite.coe_toFinset] using hA.linearIndepOn_extend hsub
  have hspan : Submodule.span K (v '' (B : Set ι)) =
      Submodule.span K (v '' (S : Set ι)) := by
    simpa only [B, Set.Finite.coe_toFinset] using hA.span_image_extend_eq_span_image hsub
  have hcard : Module.finrank K (Submodule.span K (v '' (B : Set ι))) = B.card := by
    have hh := finrank_span_eq_card (hli.linearIndependent_restrict)
    change Module.finrank K (Submodule.span K (Set.range (fun a : B => v a))) = _ at hh
    have hr : Set.range (fun a : B => v a) = v '' (B : Set ι) := by
      ext x
      constructor
      · rintro ⟨a,rfl⟩; exact ⟨a,a.property,rfl⟩
      · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
    rw [hr] at hh
    simpa using hh
  have hAB : A ⊆ B := fun a ha => hfin.mem_toFinset.mpr (hA.subset_extend hsub ha)
  have hBS : B ⊆ S := fun a ha => hTs (hfin.mem_toFinset.mp ha)
  have hmB : m ≤ B.card := by rw [← hcard,hspan]; exact hm
  obtain ⟨C,hAC,hCB,hC⟩ := Finset.exists_subsuperset_card_eq hAB hAm hmB
  exact ⟨C,hAC,hCB.trans hBS,hC,hli.mono hCB⟩
theorem q_448 (h : ℕ) (hh : 0 < h) (δ c : ℝ)
    (hδ : 0 < δ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ,
      ((t+h).choose h : ℝ) ≤ (δ*t+C)^h / ((h.factorial : ℝ)*δ^h) -
        c*(δ*t+C)^(h-1) := by
  let a : ℝ := (h.factorial : ℝ)*c*δ^(h-1) + 1/δ
  let C : ℝ := δ*((h : ℝ)+a)
  have hf : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hC : 1 ≤ C := by
    dsimp [C,a]
    rw [mul_add, mul_add, div_eq_mul_inv, one_mul, mul_inv_cancel₀ hδ.ne']
    have hN : 0 ≤ δ*(h:ℝ)+δ*((h.factorial:ℝ)*c*δ^(h-1)) := by positivity
    linarith
  refine ⟨C,hC,fun t => ?_⟩
  let x : ℝ := (t+h : ℕ)+a
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hlow : ((t+h : ℕ) : ℝ) ≤ x := by dsimp [x]; linarith
  have hT : δ*t+C = δ*x := by dsimp [C,x]; push_cast; ring
  have hpow : x^h = x^(h-1)*x := by rw [← pow_succ,Nat.sub_add_cancel hh]
  have hnum : ((t+h : ℕ) : ℝ)^h ≤ x^h - (h.factorial : ℝ)*c*δ^(h-1)*x^(h-1) := by
    have hq : ((t+h : ℕ) : ℝ)^(h-1) ≤ x^(h-1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlow _
    have hb : ((t+h : ℕ) : ℝ) ≤ x - (h.factorial : ℝ)*c*δ^(h-1) := by
      dsimp [x,a]
      linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 1) hδ.le]
    calc
      _ = ((t+h : ℕ) : ℝ)^(h-1)*((t+h : ℕ) : ℝ) := by
        rw [← pow_succ,Nat.sub_add_cancel hh]
      _ ≤ x^(h-1)*(x-(h.factorial : ℝ)*c*δ^(h-1)) :=
        mul_le_mul hq hb (Nat.cast_nonneg _) (pow_nonneg hx _)
      _ = _ := by rw [hpow]; ring
  have hb := (Nat.choose_le_pow_div h (t+h) : ((t+h).choose h : ℝ) ≤
      ((t+h : ℕ) : ℝ)^h / (h.factorial : ℝ))
  apply hb.trans
  rw [hT,mul_pow,mul_pow]
  have he : δ^h*x^h / ((h.factorial:ℝ)*δ^h) - c*(δ^(h-1)*x^(h-1)) =
      (x^h-(h.factorial:ℝ)*c*δ^(h-1)*x^(h-1))/(h.factorial:ℝ) := by
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hnum hf.le
theorem q_480 (h t : ℕ) :
    h*((t+1+h).choose (h+1)) + (t+1)*((t+h).choose h) =
      h*((t+h).choose (h+1)) + (t+1)*((t+1+h).choose h) := by
  have h₁ := Nat.choose_succ_succ (t+h) h
  have h₂ := Nat.choose_mul_succ_eq (t+h) h
  rw [show t+h+1-h = t+1 by omega] at h₂
  rw [show t+1+h = t+h+1 by omega]
  nlinarith
theorem q_291 {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (S : ℕ → Finset ι)
    (hS : ∀ t, S t ⊆ S (t+1)) (w : ι → ℝ) (δ C : ℝ)
    (hweight : ∀ t a, a ∈ S t → w a ≤ δ*t+C)
    (h : ℕ) (hrank : ∀ t, (t+h).choose h ≤
      Module.finrank K (Submodule.span K (v '' (S t : Set ι)))) (t : ℕ) :
    ∃ A : Finset ι, A ⊆ S t ∧ A.card = (t+h).choose h ∧
      LinearIndepOn K v (A : Set ι) ∧
      ∑ a ∈ A, w a ≤ δ*(h*((t+h).choose (h+1)) : ℕ) + C*((t+h).choose h) := by
  classical
  induction t with
  | zero =>
    obtain ⟨A,_,hA,hcard,hli⟩ := q_174 v (S 0) ∅
      (Finset.empty_subset _) (by simp)
      ((0+h).choose h) (by simp) (hrank 0)
    refine ⟨A,hA,hcard,hli,?_⟩
    have hb := Finset.sum_le_sum (s := A) (fun a ha => hweight 0 a (hA ha))
    simpa only [Nat.cast_zero,mul_zero,zero_add,Finset.sum_const, nsmul_eq_mul,
      hcard,Nat.choose_self,Nat.cast_one,mul_one,one_mul,Nat.choose_eq_zero_of_lt (Nat.lt_succ_self h),
      Nat.mul_zero] using hb
  | succ t ih =>
    obtain ⟨A,hA,hcard,hli,hsum⟩ := ih
    have hcount : A.card ≤ (t+1+h).choose h := by
      rw [hcard]
      exact Nat.choose_le_choose h (by omega)
    obtain ⟨B,hAB,hB,hBcard,hlB⟩ := q_174 v (S (t+1)) A
      (hA.trans (hS t)) hli ((t+1+h).choose h) hcount (hrank (t+1))
    refine ⟨B,hB,hBcard,hlB,?_⟩
    have hnew : ∑ a ∈ B \ A, w a ≤ ((B \ A).card : ℝ)*(δ*(t+1)+C) := by
      calc
        _ ≤ ∑ _a ∈ B \ A, (δ*(t+1)+C) := by
          apply Finset.sum_le_sum
          intro a ha
          have haW := hweight (t+1) a (hB (Finset.mem_sdiff.mp ha).1)
          simpa only [Nat.cast_add,Nat.cast_one] using haW
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    have hsplit : (∑ a ∈ B \ A, w a) + (∑ a ∈ A, w a) = ∑ a ∈ B, w a :=
      Finset.sum_sdiff hAB
    have hcarddiff : ((B \ A).card : ℝ) = (B.card : ℝ)-(A.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hAB,Nat.cast_sub (Finset.card_le_card hAB)]
    have hstep : (h*((t+1+h).choose (h+1)) : ℕ) +
        ((t+1)*((t+h).choose h) : ℕ) =
      (h*((t+h).choose (h+1)) : ℕ) + ((t+1)*((t+1+h).choose h) : ℕ) :=
      q_480 h t
    have hstepR : (h*((t+1+h).choose (h+1)) : ℝ) +
        ((t:ℝ)+1)*((t+h).choose h) =
      (h*((t+h).choose (h+1)) : ℝ) + ((t:ℝ)+1)*((t+1+h).choose h) := by
      exact_mod_cast hstep
    rw [hcarddiff,hcard,hBcard] at hnew
    push_cast at hsum ⊢
    have he : (δ*(t+1)+C)*(((t+1+h).choose h : ℝ)-((t+h).choose h : ℝ)) +
        (δ*(h:ℝ)*((t+h).choose (h+1))) + C*((t+h).choose h) =
      δ*(h:ℝ)*((t+1+h).choose (h+1)) + C*((t+1+h).choose h) := by
      nlinarith [congrArg (fun x : ℝ => δ*x) hstepR]
    rw [← hsplit]
    calc
      _ ≤ (( (t+1+h).choose h : ℝ)-((t+h).choose h : ℝ))*(δ*(t+1)+C) +
          (δ*((h:ℝ)*((t+h).choose (h+1))) + C*((t+h).choose h)) := add_le_add hnew hsum
      _ = _ := by nlinarith [he]
open scoped BigOperators
open MvPolynomial
noncomputable def q_37 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (a : σ →₀ ℕ) : ℝ := ∑ i, ω i*(a i : ℝ)
noncomputable def q_253 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => ⌊T/ω i⌋₊)
noncomputable def q_92 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : Finset (σ →₀ ℕ) := by
  classical
  exact (Finset.Iic (q_253 ω T)).filter fun a => q_37 ω a ≤ T
theorem q_69 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ) :
    a ∈ q_92 ω T ↔ q_37 ω a ≤ T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_,ha⟩
    intro i
    change a i ≤ ⌊T/ω i⌋₊
    apply Nat.le_floor
    apply (le_div_iff₀ (hω i)).mpr
    have hi := Finset.single_le_sum
      (fun j _ => mul_nonneg (hω j).le (Nat.cast_nonneg (a j))) (Finset.mem_univ i)
    simpa only [mul_comm (a i : ℝ)] using hi.trans ha
theorem q_419 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) {S T : ℝ} (h : S ≤ T) :
    q_92 ω S ⊆ q_92 ω T := by
  intro a ha
  exact (q_69 ω hω T a).mpr
    (((q_69 ω hω S a).mp ha).trans h)
noncomputable def q_308 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : ℕ := ∑ i, ⌊T/ω i⌋₊
theorem q_233 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ)
    (ha : q_37 ω a ≤ T) : a.sum (fun _ e => e) ≤ q_308 ω T := by
  classical
  have hs := (Finset.mem_filter.mp ((q_69 ω hω T a).mpr ha)).1
  have hb : a ≤ q_253 ω T := Finset.mem_Iic.mp hs
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_le_sum (fun i _ => hb i)
noncomputable def q_60 {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  Submodule.span K ((fun a => Ideal.Quotient.mk I (monomial a (1:K))) ''
    (q_92 ω T : Set (σ →₀ ℕ)))
instance weightedFunctions_finite {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) :
    Module.Finite K (q_60 I ω T) := by
  classical
  exact Module.Finite.span_of_finite K ((q_92 ω T).finite_toSet.image _)
noncomputable def q_32 {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) : ℕ :=
  Module.finrank K (q_60 I ω T)
theorem q_412 {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (C X : ℝ) (hC : 1 ≤ C) (hX : 0 < X)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ C * X^(ω i)) (a : σ →₀ ℕ)
    (D : ℕ) (hD : a.sum (fun _ e => e) ≤ D) :
    |((eval z (monomial a (1:ℤ)) : ℤ) : ℝ)| ≤ C^D * X^(q_37 ω a) := by
  classical
  have hprod : |((eval z (monomial a (1:ℤ)) : ℤ) : ℝ)| = ∏ i, |(z i : ℝ)|^(a i) := by
    rw [eval_monomial,one_mul,Finsupp.prod_fintype _ _ (by simp)]
    simp only [Int.cast_prod,Int.cast_pow,Finset.abs_prod,abs_pow]
  have hexp : (∏ i, (X^(ω i))^(a i)) = X^(q_37 ω a) := by
    simp_rw [← Real.rpow_mul_natCast hX.le]
    rw [← Real.rpow_sum_of_pos hX]
    rfl
  calc
    _ = ∏ i, |(z i : ℝ)|^(a i) := hprod
    _ ≤ ∏ i, (C*X^(ω i))^(a i) := Finset.prod_le_prod
      (fun i _ => pow_nonneg (abs_nonneg _) _) (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hz i) _)
    _ = C^(a.sum (fun _ e => e)) * X^(q_37 ω a) := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hexp]
      rw [Finsupp.sum_fintype _ _ (by simp)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hD) (Real.rpow_nonneg hX.le _)
end
open scoped BigOperators
open MvPolynomial
theorem q_450 (h : ℕ) (hh : 0 < h) (ν C : ℝ) (hν : 0 < ν) :
    ∃ t : ℕ, 0 < (t+h).choose h ∧
      (C+1)*((t+h).choose h : ℝ) ≤ ν*(h*((t+h).choose (h+1)) : ℕ) := by
  obtain ⟨t,ht⟩ := exists_nat_gt (((C+1)*((h:ℝ)+1))/(ν*h))
  have hp : 0 < ν*(h:ℝ) := mul_pos hν (by exact_mod_cast hh)
  have ht' := (div_lt_iff₀ hp).mp ht
  have hchoose : (h+1)*((t+h).choose (h+1)) = t*((t+h).choose h) := by
    have hc := Nat.add_one_mul_choose_eq (t+h) h
    rw [Nat.choose_succ_succ] at hc
    nlinarith
  have hr : ((h:ℝ)+1)*((t+h).choose (h+1) : ℝ) = (t:ℝ)*((t+h).choose h) := by
    exact_mod_cast hchoose
  have hL : 0 < (t+h).choose h := Nat.choose_pos (by omega)
  refine ⟨t,hL,?_⟩
  have hb := mul_le_mul_of_nonneg_right ht'.le (show (0:ℝ) ≤ (t+h).choose h by positivity)
  push_cast
  nlinarith
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open scoped BigOperators
open MvPolynomial
theorem q_399 {α : Type*} [Fintype α]
    (w : α → ℝ) (C X δ ν c Q : ℝ) (D m : ℕ)
    (hX : 1 < X)
    (hlarge : (Fintype.card α).factorial * (C^D)^(Fintype.card α) < X)
    (hL : 0 < Fintype.card α)
    (hsum : ∑ a, w a ≤ δ*(m:ℝ)+c*(Fintype.card α))
    (hmargin : (c+1)*(Fintype.card α : ℝ) ≤ ν*(m:ℝ))
    (hQ : X^(δ+ν) ≤ Q) :
    (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, (C^D * X^(w a)) < Q^m := by
  classical
  have hpos : 0 < X := lt_trans zero_lt_one hX
  have hprod : (∏ a, (C^D * X^(w a))) = (C^D)^(Fintype.card α)*X^(∑ a, w a) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Real.rpow_sum_of_pos hpos]
  have hweight : (∑ a, w a)+1 ≤ (δ+ν)*(m:ℝ) := by
    have hcL : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast hL
    nlinarith
  calc
    _ = ((Fintype.card α).factorial * (C^D)^(Fintype.card α))*X^(∑ a, w a) := by rw [hprod]; ring
    _ < X*X^(∑ a, w a) := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hpos _)
    _ = X^((∑ a, w a)+1) := by rw [Real.rpow_add hpos,Real.rpow_one,mul_comm]
    _ ≤ X^((δ+ν)*(m:ℝ)) := Real.rpow_le_rpow_of_exponent_le hX.le hweight
    _ = (X^(δ+ν))^m := Real.rpow_mul_natCast hpos.le _ m
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) hQ m
theorem q_169 {σ α K : Type*}
    [Fintype α] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial σ K)) (a : α → (σ →₀ ℕ))
    (hli : LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (a i) (1:K))))
    (c : α → ℚ) (hc : c ≠ 0) :
    MvPolynomial.map (algebraMap ℚ K) (∑ i, monomial (a i) (c i)) ∉ I := by
  intro hp
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have he (i : α) : monomial (a i) (algebraMap ℚ K (c i)) =
      (algebraMap ℚ K (c i)) • monomial (a i) (1:K) := by
    simp only [smul_monomial,smul_eq_mul,mul_one]
  simp only [map_sum,MvPolynomial.map_monomial,he] at hz
  change ∑ i, (Ideal.Quotient.mkₐ K I) ((algebraMap ℚ K (c i)) • monomial (a i) (1:K)) = 0 at hz
  simp only [map_smul] at hz
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (fun i => algebraMap ℚ K (c i)) hz
  apply hc
  funext i
  change c i = 0
  exact (algebraMap ℚ K).injective (by simpa only [map_zero] using hcoeff i)
theorem q_377 {σ α : Type*} [Fintype α]
    (a : α → (σ →₀ ℕ)) (c : α → ℚ) (D : ℕ)
    (hD : ∀ i, (a i).sum (fun _ e => e) ≤ D) :
    (∑ i, monomial (a i) (c i)).totalDegree ≤ D := by
  exact totalDegree_finsetSum_le (fun i _ => (totalDegree_monomial_le _ _).trans (hD i))
theorem q_424 {σ α : Type*} [Fintype α]
    (a : α → (σ →₀ ℕ)) (c : α → ℚ) (z : σ → ℤ)
    (hz : ∑ i, c i * (eval z (monomial (a i) (1:ℤ)) : ℚ) = 0) :
    eval (fun i => (z i : ℚ)) (∑ i, monomial (a i) (c i)) = 0 := by
  rw [map_sum]
  convert hz using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_monomial,one_mul,Finsupp.prod,Int.cast_prod,Int.cast_pow]
end
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
theorem q_1.eval_chart {n : ℕ} (P : q_1 n) (z : Fin n → ℤ)
    (p : MvPolynomial (Fin n) ℤ) :
    eval (fun i => z ((Equiv.Set.sumCompl P.free) i))
      (rename (Equiv.Set.sumCompl P.free).symm p) = eval z p := by
  rw [eval_rename]
  simp [Function.comp_def]
theorem q_1.minor_chart {n : ℕ} (P : q_1 n) (z : Fin n → ℤ) :
    (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z ((Equiv.Set.sumCompl P.free) a))
        (pderiv (Sum.inr j) (rename (Equiv.Set.sumCompl P.free).symm (P.equations i))))).det =
      eval z P.minor := by
  classical
  let e := Equiv.Set.sumCompl P.free
  have he (j : ↥(P.freeᶜ)) : e.symm j.val = Sum.inr j := by
    apply e.injective
    simp [e]
  have hm : (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))))) =
      Matrix.of (fun i j : ↥(P.freeᶜ) => eval z (pderiv j.val (P.equations i))) := by
    ext i j
    change eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))) = _
    rw [← he j,pderiv_rename e.symm.injective]
    exact P.eval_chart z _
  change (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))))).det = _
  rw [hm]
  exact ((eval z).map_det (fun i j : ↥(P.freeᶜ) => pderiv j.val (P.equations i))).symm
theorem q_1.residue_relation {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (P : q_1 n) (z : Fin n → ℤ) (hz : ∀ j, eval z (P.equations j) = 0)
    (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z P.minor)
    (m : ℕ) (R : α → MvPolynomial (Fin n) ℤ) (w : β → Fin n → ℤ)
    (hw : ∀ p ∈ Q, ∀ b j, (p:ℤ) ∣ w b j-z j)
    (hroot : ∀ b j, eval (w b) (P.equations j) = 0)
    (hm : ∀ r : α → (P.free →₀ ℕ), Function.Injective r → m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (R a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p:ℝ))^m) :
    ∃ c : α → ℚ, c ≠ 0 ∧ ∀ b, ∑ a, c a * (eval (w b) (R a) : ℚ) = 0 := by
  classical
  let e := Equiv.Set.sumCompl P.free
  have hc := q_260
    (fun j => rename e.symm (P.equations j)) (fun j => z (e j))
    (fun j => (P.eval_chart z _).trans (hz j)) Q hprime
    (fun p hp => by rw [P.minor_chart z]; exact hgood p hp) m
    (fun a => rename e.symm (R a)) (fun b j => w b (e j))
    (fun p hp b j => hw p hp b (e j))
    (fun b j => (P.eval_chart (w b) _).trans (hroot b j)) hm B
    (fun a b => by rw [P.eval_chart]; exact hB a b) hlt
  simpa only [eval_rename,Function.comp_def,Equiv.apply_symm_apply] using hc
theorem q_313 {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i)
    (h : ℕ) (hh : 0 < h) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hboxC : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ I : Ideal (MvPolynomial (Fin n) ℂ),
      (∀ T : ℝ, 1 ≤ T → T^h / ((h.factorial : ℝ)*δ^h) - c*T^(h-1) ≤
        q_32 I ω T) →
      ∀ P : q_1 n, Nat.card P.free = h →
      ∀ z : Fin n → ℤ, (∀ j, eval z (P.equations j) = 0) →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z P.minor) → X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      ∀ S : Finset (Fin n → ℤ),
      (∀ p ∈ Q, ∀ w ∈ S, ∀ j, (p:ℤ) ∣ w j-z j) →
      (∀ w ∈ S, ∀ j, eval w (P.equations j) = 0) →
      (∀ w ∈ S, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∃ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D ∧ p ∉ I ∧
        ∀ w ∈ S, eval (fun i => (w i : ℂ)) p = 0 := by
  classical
  obtain ⟨C,hC,hshift⟩ := q_448 h hh δ c hδ hc
  obtain ⟨t,hL,hmargin⟩ := q_450 h hh ν C hν
  let D := q_308 ω (δ*t+C)
  let L := (t+h).choose h
  let m := h*((t+h).choose (h+1))
  refine ⟨D,max 1 ((L.factorial : ℝ)*(Cbox^D)^L),?_⟩
  intro X hX I hH P hfree z hz Q hprime hgood hQ S hw hroot hbox
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hlarge : (L.factorial : ℝ)*(Cbox^D)^L < X := lt_of_le_of_lt (le_max_right _ _) hX
  let U := fun t : ℕ => q_92 ω (δ*t+C)
  have hU : ∀ t, U t ⊆ U (t+1) := by
    intro t
    apply q_419 ω hω
    push_cast
    linarith
  have hweight : ∀ t a, a ∈ U t → q_37 ω a ≤ δ*t+C := by
    intro t a ha
    exact (q_69 ω hω _ a).mp ha
  have hr : ∀ t, (t+h).choose h ≤ Module.finrank ℂ
      (Submodule.span ℂ ((fun a => Ideal.Quotient.mk I (monomial a (1:ℂ))) '' (U t : Set _))) := by
    intro t
    have hT : 1 ≤ δ*(t:ℝ)+C := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg t)]
    exact_mod_cast (hshift t).trans (hH _ hT)
  obtain ⟨A,hA,hcard,hli,hsum⟩ := q_291
    (fun a => Ideal.Quotient.mk I (monomial a (1:ℂ))) U hU (q_37 ω) δ C hweight h hr t
  have hcard' : Fintype.card A = L := by simpa only [Fintype.card_coe] using hcard
  have hD : ∀ a : A, a.val.sum (fun _ e => e) ≤ D := fun a =>
    q_233 ω hω _ a.val (hweight t a.val (hA a.property))
  have hsum' : ∑ a : A, q_37 ω a.val ≤ δ*(m:ℝ)+C*(Fintype.card A) := by
    rw [hcard',Finset.sum_coe_sort]
    exact hsum
  have hmargin' : (C+1)*(Fintype.card A : ℝ) ≤ ν*(m:ℝ) := by
    rw [hcard']; exact hmargin
  have hlt : (Fintype.card A).factorial * ∏ a : A, (Cbox^D*X^(q_37 ω a.val)) <
      (∏ p ∈ Q, (p:ℝ))^m := q_399
        (fun a : A => q_37 ω a.val) Cbox X δ ν C _ D m hX1
        (by rwa [hcard']) (by rwa [hcard']) hsum' hmargin' hQ
  have hf : Fintype.card P.free = h := by simpa only [Nat.card_eq_fintype_card] using hfree
  obtain ⟨c,hc,hrel⟩ := P.residue_relation z hz Q hprime hgood m
    (fun a : A => monomial a.val (1:ℤ)) (fun w : S => w.val)
    (fun p hp w j => hw p hp w.val w.property j)
    (fun w j => hroot w.val w.property j)
    (fun r hr => by
      have hm := q_288 r hr t (by rw [hf]; exact hcard'.symm.le)
      simpa only [hf,q_38] using hm)
    (fun a : A => Cbox^D*X^(q_37 ω a.val))
    (fun a w => q_412 ω Cbox X hboxC (lt_trans zero_lt_one hX1)
      w.val (hbox w.val w.property) a.val D (hD a)) hlt
  have hp := q_169 I _ hli.linearIndependent_restrict c hc
  let p : MvPolynomial (Fin n) ℚ := ∑ a : A, monomial a.val (c a)
  have hpdeg : (MvPolynomial.map (algebraMap ℚ ℂ) p).totalDegree = p.totalDegree := by
    simp only [totalDegree,support_map_of_injective p (f := algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective]
  refine ⟨MvPolynomial.map (algebraMap ℚ ℂ) p,
    hpdeg.le.trans (q_377 _ _ D hD),hp,?_⟩
  intro w hw
  have he := congrArg (algebraMap ℚ ℂ) (q_424 _ _ w (hrel ⟨w,hw⟩))
  rw [MvPolynomial.eval_map]
  simpa only [MvPolynomial.eval₂_comp,map_zero,Function.comp_def,map_intCast] using he
end
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
theorem q_1.equation_vanishes {n : ℕ} {K : Type*} [Field K] [CharZero K]
    {P : q_1 n} {I : Ideal (MvPolynomial (Fin n) K)}
    (hP : P.On I) {z : Fin n → ℤ} (hz : q_64 I z) (j : ↥(P.freeᶜ)) :
    eval z (P.equations j) = 0 := by
  apply Int.cast_injective (α := K)
  rw [Int.cast_zero,← q_218]
  exact hz _ (hP.2.1 j)
theorem q_357 {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (q : ℕ) (hq : 0 < q) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hCbox : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ (r E : ℕ) (G : KernelGeometry n) (d : ℕ → ℕ) (A h e i : ℕ),
      D ≤ d i → d i ≤ E →
      (∀ w ∈ G.points, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (z : Fin n → ℤ), z ∈ G.points →
      ∀ s : Ideal (MvPolynomial (Fin n) ℂ) × q_1 n,
      q_29 G h (q_4 n d A h e i) z s →
      q_0 s.1 = q →
      (∀ T : ℝ, 1 ≤ T → T^q / ((q.factorial : ℝ)*δ^q) - c*T^(q-1) ≤
        q_32 s.1 ω T) →
      ∀ B : Fin r → Finset ℕ, ∀ Q : Finset ℕ,
      Q ⊆ q_9 B i → (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z s.2.minor) → X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      q_0 (q_81 G d A h e z i s (q_22 (E := E) G d z i s B)).1 <
        q_0 s.1 := by
  classical
  obtain ⟨D,X₀,hcut⟩ := q_313 ω hω q hq δ ν c Cbox hδ hν hc hCbox
  refine ⟨D,X₀,?_⟩
  intro X hX r E G d A h e i hD hE hbox z hz s hs hdim hH B Q hQ hprime hgood hprod
  let S := q_98 G.points s.1 z (q_9 B i)
  obtain ⟨p,hpD,hpI,hpS⟩ := hcut X hX s.1 hH s.2 (hs.2.1.1.trans hdim) z
    (fun j => q_1.equation_vanishes hs.2.1 hs.2.2.2.1 j) Q hprime hgood hprod S
    (fun p hp w hw j => (Finset.mem_filter.mp hw).2.2 p (hQ hp) j)
    (fun w hw j => q_1.equation_vanishes hs.2.1 (Finset.mem_filter.mp hw).2.1 j)
    (fun w hw j => hbox w (Finset.mem_filter.mp hw).1 j)
  apply (q_171 (E := E) G d A h e z hz i s hs B).2.2.2.2.2
  intro hsub
  apply hpI
  apply hsub
  exact (q_304 hE S p).mpr ⟨hpD.trans hD,hpS⟩
theorem q_64.eq_of_zeroDim {n : ℕ} {K : Type*} [Field K] [CharZero K]
    {I : Ideal (MvPolynomial (Fin n) K)} [I.IsPrime]
    (hd : q_0 I = 0) {z w : Fin n → ℤ}
    (hz : q_64 I z) (hw : q_64 I w) : z = w := by
  have hI := q_130 I hd (fun j => (z j : K)) hz
  funext j
  apply Int.cast_injective (α := K)
  have hmem : X j - C (z j : K) ∈ I := by
    rw [hI,RingHom.mem_ker]
    simp
  have he : (w j : K) - (z j : K) = 0 := by simpa using hw _ hmem
  exact (sub_eq_zero.mp he).symm
theorem q_421 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points)
    (hd : q_0 (q_2 (E := E) G d A h e start B i z).1 = 0) :
    (S.filter fun w => q_41 (E := E) G d A h e start B i w =
      q_41 (E := E) G d A h e start B i z).card ≤ 1 := by
  classical
  let I := (q_2 (E := E) G d A h e start B i z).1
  have hz := q_30 (E := E) G d A h e start hs B i z
  let : I.IsPrime := hz.1.1
  apply (Finset.card_le_card (t := {z}) ?_).trans (by simp)
  intro w hw
  have he := congrArg (fun x => x.1) (Finset.mem_filter.mp hw).2
  change q_2 (E := E) G d A h e start B i w =
    q_2 (E := E) G d A h e start B i z at he
  have hw := (q_30 (E := E) G d A h e start hs B i w).2.2.2.1
  rw [he] at hw
  exact Finset.mem_singleton.mpr (Subtype.ext (q_64.eq_of_zeroDim hd hw hz.2.2.2.1))
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
noncomputable def q_96 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (z : G.points) : ℤ :=
  ((q_17 (q_22 (E := E) G d z.val) (q_81 G d A h e z.val)
    m 0 (start z) B).map (fun t => eval z.val t.2.minor)).prod
theorem q_241 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (z : G.points) (i : ℕ) (hi : i ≤ m) :
    eval z.val (q_2 (E := E) G d A h e start B i z).2.minor ∣
      q_96 (E := E) G d A h e m start B z := by
  apply List.dvd_prod
  apply List.mem_map.mpr
  exact ⟨q_2 (E := E) G d A h e start B i z,
    q_349 _ _ m i 0 _ B hi,rfl⟩
def q_54 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (ξ : ℝ) (z : G.points) : Prop :=
  ∀ j, ((∑ p ∈ B j, if (p : ℤ) ∣ q_96 (E := E) G d A h e m start B z
    then (1 : ℝ) else 0) / (B j).card) ≤ ξ
theorem q_340 {α : Type*} (S : Finset α) (P : α → Prop)
    [DecidablePred P] (ξ : ℝ)
    (h : (∑ p ∈ S, if P p then (1 : ℝ) else 0) / S.card ≤ ξ) :
    ((S.filter P).card : ℝ) ≤ ξ*S.card := by
  by_cases hs : S.card = 0
  · have he := Finset.card_eq_zero.mp hs
    subst S
    simp
  have hp : (0 : ℝ) < S.card := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  rw [Finset.sum_boole] at h
  exact (div_le_iff₀ hp).mp h
theorem q_54.bad_minor {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (B : Fin r → Finset ℕ) (ξ : ℝ) (z : G.points)
    (hz : q_54 (E := E) G d A h e m start B ξ z) (i : ℕ) (hi : i ≤ m) (j : Fin r) :
    (((B j).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
      (q_2 (E := E) G d A h e start B i z).2.minor).card : ℝ) ≤ ξ*(B j).card := by
  have hsub : ((B j).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
      (q_2 (E := E) G d A h e start B i z).2.minor) ⊆
      ((B j).filter fun p : ℕ => (p:ℤ) ∣ q_96 (E := E) G d A h e m start B z) := by
    intro p hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,hd.trans (q_241 G d A h e m start B z i hi)⟩
  calc
    _ ≤ (((B j).filter fun p : ℕ =>
        (p:ℤ) ∣ q_96 (E := E) G d A h e m start B z).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := q_340 _ _ ξ (hz j)
theorem q_272 {r : ℕ} (B : Fin r → Finset ℕ)
    (hdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b)) (i : ℕ) (v : ℤ)
    (X ζ ξ : ℝ) (hX : 1 ≤ X) (hζ : 0 ≤ ζ)
    (hlo : ∀ j p, p ∈ B j → X^ζ ≤ (p:ℝ))
    (hbad : ∀ j, (((B j).filter fun p : ℕ => (p:ℤ) ∣ v).card : ℝ) ≤ ξ*(B j).card) :
    X^((1-ξ)*ζ*∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i), ((B j).card : ℝ)) ≤
      ∏ p ∈ (q_9 B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ v), (p:ℝ) := by
  classical
  let J := Finset.univ.filter (fun j : Fin r => j.val ≤ i)
  let Q := (q_9 B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ v)
  have hg (j : Fin r) : (1-ξ)*(B j).card ≤
      (((B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v).card : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not (s := B j) (fun p : ℕ => (p:ℤ) ∣ v)
    have hcr : (((B j).filter fun p : ℕ => (p:ℤ) ∣ v).card : ℝ) +
      (((B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v).card : ℝ) = (B j).card := by exact_mod_cast hc
    nlinarith [hbad j]
  have heq : Q = J.biUnion (fun j => (B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v) := by
    ext p
    simp only [Q,J,q_9,Finset.mem_filter,Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j,hj,hp⟩,hg⟩
      exact ⟨j,hj,hp,hg⟩
    · rintro ⟨j,hj,hp,hg⟩
      exact ⟨⟨j,hj,hp⟩,hg⟩
  have hpair : (J : Set (Fin r)).PairwiseDisjoint
      (fun j => (B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v) := by
    intro a _ b _ hab
    exact (hdisj a b hab).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard : (1-ξ)*(∑ j ∈ J, ((B j).card : ℝ)) ≤ (Q.card : ℝ) := by
    rw [heq,Finset.card_biUnion hpair,Nat.cast_sum,Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hg j)
  calc
    _ ≤ X^(ζ*(Q.card : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      nlinarith
    _ = (X^ζ)^Q.card := Real.rpow_mul_natCast (zero_le_one.trans hX) ζ Q.card
    _ = ∏ _p ∈ Q, X^ζ := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro p _; exact Real.rpow_nonneg (zero_le_one.trans hX) _
      · intro p hp
        obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
        exact hlo j p hpj
end
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
noncomputable def q_270 (r : ℕ) (P : ℕ → Prop) : ℕ :=
  Nat.find (show ∃ i, i = r ∨ P i from ⟨r,Or.inl rfl⟩)
theorem q_501 (r : ℕ) (P : ℕ → Prop) : q_270 r P ≤ r :=
  Nat.find_min' _ (Or.inl rfl)
theorem q_505 (r : ℕ) (P : ℕ → Prop) : q_270 r P = r ∨ P (q_270 r P) :=
  Nat.find_spec (show ∃ i, i = r ∨ P i from ⟨r,Or.inl rfl⟩)
theorem q_461 (r : ℕ) (P : ℕ → Prop) {i : ℕ} (hi : i < q_270 r P) : ¬ P i :=
  fun hp => Nat.find_min _ hi (Or.inr hp)
theorem q_176 (r : ℕ) (dim : ℕ → ℕ) (Ex : ℕ → Prop)
    (hzero : dim 0 ≤ r) (hmono : ∀ i < r, dim (i+1) ≤ dim i)
    (hstep : ∀ i < r, ¬ Ex i → dim i = r-i → dim (i+1) < dim i) :
    ∀ i ≤ q_270 r (fun i => Ex i ∨ dim i = 0), dim i ≤ r-i := by
  intro i
  induction i with
  | zero => intro _; simpa using hzero
  | succ i ih =>
    intro hi
    have his : i < q_270 r (fun i => Ex i ∨ dim i = 0) := by omega
    have hir : i < r := lt_of_lt_of_le his (q_501 _ _)
    have hd := ih his.le
    have hstop := q_461 r (fun i => Ex i ∨ dim i = 0) his
    by_cases he : dim i = r-i
    · have hs := hstep i hir (fun h => hstop (Or.inl h)) he
      omega
    · have hm := hmono i hir
      omega
theorem q_486 (r : ℕ) (dim : ℕ → ℕ) (Ex : ℕ → Prop)
    (hzero : dim 0 ≤ r) (hmono : ∀ i < r, dim (i+1) ≤ dim i)
    (hstep : ∀ i < r, ¬ Ex i → dim i = r-i → dim (i+1) < dim i) :
    let t := q_270 r (fun i => Ex i ∨ dim i = 0)
    Ex t ∨ dim t = 0 := by
  dsimp only
  rcases q_505 r (fun i => Ex i ∨ dim i = 0) with he | hp
  · right
    have hd := q_176 r dim Ex hzero hmono hstep
      (q_270 r (fun i => Ex i ∨ dim i = 0)) le_rfl
    rw [he,Nat.sub_self] at hd
    rw [he]
    exact Nat.eq_zero_of_le_zero hd
  · exact hp
theorem q_372 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points) :
    (S.filter fun w => q_41 (E := E) G d A h e start B i w =
      q_41 (E := E) G d A h e start B i z).card ≤
    (G.points.filter (q_64 (q_2 (E := E) G d A h e start B i z).1)).card := by
  classical
  let F := S.filter fun w => q_41 (E := E) G d A h e start B i w =
    q_41 (E := E) G d A h e start B i z
  have hsub : F.image (fun w : G.points => w.val) ⊆
      G.points.filter (q_64 (q_2 (E := E) G d A h e start B i z).1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w,hw,hwx⟩
    rw [← hwx]
    have hn := (Finset.mem_filter.mp hw).2
    have he := congrArg Prod.fst hn
    change q_2 (E := E) G d A h e start B i w =
      q_2 (E := E) G d A h e start B i z at he
    have hp := (q_30 (E := E) G d A h e start hs B i w).2.2.2.1
    rw [he] at hp
    exact Finset.mem_filter.mpr ⟨w.property,hp⟩
  calc
    _ = (F.image (fun w : G.points => w.val)).card :=
      (Finset.card_image_of_injective F Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card hsub
theorem q_406 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) :
    q_0 (q_2 (E := E) G d A h e start B (i+1) z).1 ≤
      q_0 (q_2 (E := E) G d A h e start B i z).1 := by
  rw [q_89]
  exact (q_171 (E := E) G d A h e z.val z.property i _
    (q_30 (E := E) G d A h e start hs B i z) B).2.2.2.2.1
end
section
open MvPolynomial
open scoped BigOperators
open scoped Classical
open scoped Classical
end
theorem q_494 (N M : ℕ) (hM : M ≠ 0) :
    ∃ P : Finset ℕ, P.card = N ∧ ∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2^N*M := by
  induction N with
  | zero => exact ⟨∅,by simp,by simp⟩
  | succ N ih =>
    obtain ⟨P,hcard,hP⟩ := ih
    obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2^N*M)
      (Nat.mul_ne_zero (by positivity) hM)
    have hnot : p ∉ P := fun h => (not_lt_of_ge (hP p h).2.2) hlo
    refine ⟨insert p P,by simp [hnot,hcard],?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨hp,?_,?_⟩
      · exact (Nat.le_mul_of_pos_left M (by positivity : 0 < 2^N)).trans_lt hlo
      · simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi
    · obtain ⟨hqprime,hqlo,hqhi⟩ := hP q hq
      refine ⟨hqprime,hqlo,hqhi.trans ?_⟩
      exact Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.le_succ N))
theorem q_462 (r t : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∃ P : Fin r → Finset ℕ,
      (∀ i, (P i).card = t) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      ∀ i p, p ∈ P i → p.Prime ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2^(r*t+1)*x := by
  classical
  obtain ⟨Q,hcard,hQ⟩ := q_494 (r*t) ⌈x⌉₊
    (Nat.ne_of_gt (Nat.ceil_pos.mpr (zero_lt_one.trans_le hx)))
  let e : (Fin r × Fin t) ≃ Q := Fintype.equivOfCardEq (by simp [hcard])
  let P : Fin r → Finset ℕ := fun i => Finset.univ.image (fun j => (e (i,j)).val)
  have hinj (i : Fin r) : Function.Injective (fun j => (e (i,j)).val) := by
    intro j k he
    exact (Prod.mk.inj (e.injective (Subtype.ext he))).2
  refine ⟨P,?_,?_,?_⟩
  · intro i
    simp only [P,Finset.card_image_of_injective _ (hinj i),Finset.card_univ,Fintype.card_fin]
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hpi
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hpj
    exact hij (Prod.mk.inj (e.injective (Subtype.ext (ha.trans hb.symm)))).1
  · intro i p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hprime,hlo,hhi⟩ := hQ _ (e (i,j)).property
    refine ⟨hprime,(Nat.le_ceil x).trans (by exact_mod_cast hlo.le),?_⟩
    have hc : (⌈x⌉₊ : ℝ) ≤ 2*x := (Nat.ceil_lt_add_one (zero_le_one.trans hx)).le.trans (by linarith)
    calc
      ((e (i,j)).val : ℝ) ≤ (2 : ℝ)^(r*t)*(⌈x⌉₊ : ℝ) := by exact_mod_cast hhi
      _ ≤ 2^(r*t)*(2*x) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2^(r*t+1)*x := by rw [pow_succ]; ring
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
def q_74 (n A h : ℕ) (chooseDegree : ℕ → ℕ → ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | i+1 => q_36 n A h
      (q_12 (chooseDegree i (q_74 n A h chooseDegree e i)) h
        (q_74 n A h chooseDegree e i))
theorem q_286 (n A h e : ℕ) (chooseDegree : ℕ → ℕ → ℕ) :
    ∀ i, q_4 n (fun j => chooseDegree j (q_74 n A h chooseDegree e j))
      A h e i = q_74 n A h chooseDegree e i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => simp only [q_4,q_74,ih]
theorem q_373 (n A h e r : ℕ) (chooseDegree : ℕ → ℕ → ℕ) :
    ∃ d : ℕ → ℕ, ∃ E : ℕ, ∀ i < r,
      d i = chooseDegree i (q_4 n d A h e i) ∧ d i ≤ E := by
  let d := fun j => chooseDegree j (q_74 n A h chooseDegree e j)
  refine ⟨d,(Finset.range r).sup d,?_⟩
  intro i hi
  refine ⟨?_,Finset.le_sup (f := d) (Finset.mem_range.mpr hi)⟩
  dsimp only [d]
  rw [q_286]
theorem q_285 (a γ ζ : ℝ) (T t : ℕ)
    (ha : 0 ≤ a) (hγ : 0 < γ) (hζ : 0 < ζ) (hwidth : ζ*T ≤ γ)
    (hlo : ⌊(a+γ)/ζ⌋₊ < t) (hhi : t ≤ ⌊(a+γ)/ζ⌋₊+T) :
    a+γ ≤ ζ*t ∧ ζ*t ≤ a+2*γ := by
  have hx : 0 ≤ (a+γ)/ζ := div_nonneg (by linarith) hζ.le
  have hfloor : (⌊(a+γ)/ζ⌋₊:ℝ) ≤ (a+γ)/ζ := Nat.floor_le hx
  have ht : (a+γ)/ζ < (t:ℝ) := (Nat.floor_lt hx).mp hlo
  have htc : (t:ℝ) ≤ (⌊(a+γ)/ζ⌋₊:ℝ)+T := by exact_mod_cast hhi
  constructor
  · exact (div_lt_iff₀ hζ).mp ht |>.le.trans_eq (mul_comm _ _)
  · have hh := (le_div_iff₀ hζ).mp hfloor
    nlinarith
theorem q_327 {r : ℕ} (a δ : Fin r → ℝ) (t : Fin r → ℕ)
    (γ ζ ξ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 < γ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hloss : ξ*((∑ i, a i)+(r:ℝ)*γ) ≤ γ/2)
    (hwidth : ∀ i, a i+γ ≤ ζ*t i)
    (hδ : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j) :
    ∀ i, δ i+γ/2 ≤ (1-ξ)*ζ*∑ j ∈
      Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), (t j:ℝ) := by
  classical
  intro i
  let J := Finset.univ.filter (fun j : Fin r => j.val ≤ i.val)
  have hiJ : i ∈ J := by simp [J]
  have hcard : 1 ≤ J.card := Finset.one_le_card.mpr ⟨i,hiJ⟩
  have hcardr : J.card ≤ r := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hs : ∑ j ∈ J, a j ≤ ∑ j, a j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => ha j)
  have hsum : (∑ j ∈ J, a j)+(J.card:ℝ)*γ ≤ ζ*∑ j ∈ J, (t j:ℝ) := by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      using Finset.sum_le_sum (fun j (_ : j ∈ J) => hwidth j)
  have hcr : (J.card:ℝ) ≤ r := by exact_mod_cast hcardr
  have hc1 : (1:ℝ) ≤ J.card := by exact_mod_cast hcard
  have hg : γ ≤ (J.card:ℝ)*γ := by nlinarith
  have hsmall : ξ*((∑ j ∈ J, a j)+(J.card:ℝ)*γ) ≤ γ/2 :=
    (mul_le_mul_of_nonneg_left (by nlinarith) hξ0).trans hloss
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hξ1)
  have hd := hδ i
  change δ i ≤ ∑ j ∈ J, a j at hd
  dsimp only [J] at *
  nlinarith
end
section
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
theorem q_212 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (M b : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)) (T : ℕ)
    (Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z ∈ S, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z ∈ S, q_0 (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S,
      ((B i).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
        (q_2 (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hcut : ∀ i < r, ∀ z ∈ S,
      ¬ Ex i (q_2 (E := E) G d A h e start B i z).1 →
      q_0 (q_2 (E := E) G d A h e start B i z).1 = r-i →
      q_0 (q_2 (E := E) G d A h e start B (i+1) z).1 <
        q_0 (q_2 (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z ∈ S,
      Ex i (q_2 (E := E) G d A h e start B i z).1 →
      (G.points.filter (q_64 (q_2 (E := E) G d A h e start B i z).1)).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then q_31 n d A h e B M b
        (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let dim := fun z i => q_0 (q_2 (E := E) G d A h e start B i z).1
  let ex := fun z i => Ex i (q_2 (E := E) G d A h e start B i z).1
  let stop := fun z => q_270 r (fun i => ex z i ∨ dim z i = 0)
  have hm (z) (i) (_hi : i < r) : dim z (i+1) ≤ dim z i :=
    q_406 G d A h e start hs B i z
  have hz (z) (hz : z ∈ S) : dim z 0 ≤ r := hroot z hz
  have hc (z) (hz : z ∈ S) (i) (hi : i < r) :
      ¬ ex z i → dim z i = r-i → dim z (i+1) < dim z i := hcut i hi z hz
  have hd (z) (hz' : z ∈ S) := q_176 r (dim z) (ex z) (hz z hz') (hm z) (hc z hz')
  have ht (z) (hz' : z ∈ S) := q_486 r (dim z) (ex z) (hz z hz') (hm z) (hc z hz')
  apply q_442 G d A h e start hs B S stop M b (fun k => r-k.val) L T
    hstart (fun _ _ => q_501 _ _) hM hprime hupper
  · intro i z hz hi
    exact hd z hz i.val hi.le
  · intro i z hz _
    exact hbad i z hz
  · intro i hi z hz hzi
    have hsub : (S.filter fun w => stop w = i ∧ q_41 (E := E) G d A h e start B i w =
        q_41 (E := E) G d A h e start B i z) ⊆
        S.filter (fun w => q_41 (E := E) G d A h e start B i w =
        q_41 (E := E) G d A h e start B i z) := by
      intro w hw
      obtain ⟨hw,_,hn⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hw,hn⟩
    apply (Finset.card_le_card hsub).trans
    have hterm : ex z i ∨ dim z i = 0 := by
      have hh := ht z hz
      change ex z (stop z) ∨ dim z (stop z) = 0 at hh
      simpa only [hzi] using hh
    rcases hterm with he | he
    · exact (q_372 G d A h e start hs B i z S).trans (hex i hi z hz he)
    · exact (q_421 G d A h e start hs B i z S he).trans hT
end
section
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
theorem q_371 {n : ℕ} (G : KernelGeometry n) (A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hd : q_0 I ≤ h) (he : q_16 I ≤ e)
    (hG : ∀ z ∈ G.points, q_64 I z) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n),
      L.length ≤ q_19 n A h e ∧
    ∃ start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n,
      ∀ z, start z ∈ L ∧ q_29 G h (q_36 n A h e) z.val (start z) ∧
        I ≤ (start z).1 ∧ q_103 (start z).1 G.points A := by
  classical
  obtain ⟨L,hL,hgood,hcover⟩ := q_146 A h e I hd he G.points hG
    G.height G.one_le_height G.bounded
  choose start hstart hcov using fun z : G.points => hcover z.val z.property
  refine ⟨L,hL,start,fun z => ⟨hstart z,?_,?_,?_⟩⟩
  · have hs := hgood (start z) (hstart z)
    exact ⟨⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hcov z⟩
  · exact (hgood _ (hstart z)).2.1
  · exact (hgood _ (hstart z)).2.2.2.2.2.2
theorem q_407 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hstart : ∀ z, I ≤ (start z).1 ∧ q_103 (start z).1 G.points A)
    (i : ℕ) (z : G.points) :
    I ≤ (q_2 (E := E) G d A h e start B i z).1 ∧
      q_103 (q_2 (E := E) G d A h e start B i z).1 G.points A := by
  induction i with
  | zero => exact hstart z
  | succ i ih =>
    have step := q_171 (E := E) G d A h e z.val z.property i _
      (q_30 (E := E) G d A h e start hs B i z) B
    rw [q_89]
    refine ⟨ih.1.trans step.2.2.1,?_⟩
    exact ((q_168 G (d i) A h (q_4 n d A h e i) _ _
      (q_30 (E := E) G d A h e start hs B i z).1).2.1 _ step.2.1).1.2.2.2.2.2.2
end
section
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
theorem q_422 {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)
    (hs : ∀ z, q_29 G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (M : Fin r → ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × q_1 n)) (T : ℕ)
    (Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z, q_0 (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hhalf : (G.points.card:ℝ)/2 ≤ (Finset.univ.filter
      (q_54 (E := E) G d A h e r start B ξ)).card)
    (hcut : ∀ i < r, ∀ z, q_54 (E := E) G d A h e r start B ξ z →
      ¬ Ex i (q_2 (E := E) G d A h e start B i z).1 →
      q_0 (q_2 (E := E) G d A h e start B i z).1 = r-i →
      q_0 (q_2 (E := E) G d A h e start B (i+1) z).1 <
        q_0 (q_2 (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z, Ex i (q_2 (E := E) G d A h e start B i z).1 →
      (G.points.filter (q_64 (q_2 (E := E) G d A h e start B i z).1)).card ≤ T) :
    G.points.card ≤ 2*(∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then q_31 n d A h e B M
        (fun k => ⌊ξ*(B k).card⌋₊) (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let S := Finset.univ.filter (q_54 (E := E) G d A h e r start B ξ)
  have hS (z) (hz : z ∈ S) : q_54 (E := E) G d A h e r start B ξ z :=
    (Finset.mem_filter.mp hz).2
  have hc := q_212 G d A h e start hs B S M
    (fun k => ⌊ξ*(B k).card⌋₊) L T Ex (fun z _ => hstart z) hT (fun z _ => hroot z)
    hM hprime hupper
    (fun i z hz => (Nat.le_floor_iff (mul_nonneg hξ (Nat.cast_nonneg _))).mpr
      (q_54.bad_minor G d A h e r start B ξ z (hS z hz) i.val i.isLt.le i))
    (fun i hi z hz => hcut i hi z (hS z hz)) (fun i hi z _ => hex i hi z)
  have hhalf' : G.points.card ≤ 2*S.card := by
    have hh : (G.points.card : ℝ) ≤ 2*(S.card : ℝ) := by linarith
    exact_mod_cast hh
  exact hhalf'.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hc)
end
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
theorem q_300 {r : ℕ} (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ)
    (U : Fin r → ℕ) (q : Fin r → ℕ) (K ξ : ℝ) (hK : 1 ≤ K) (hξ : 0 ≤ ξ) :
    ∃ C : Fin r → ℝ, (∀ i, 1 ≤ C i) ∧
    ∀ X ζ : ℝ, 1 ≤ X → 0 ≤ ζ → ∀ (B : Fin r → Finset ℕ) (M : Fin r → ℕ),
      (∀ i, (B i).card ≤ U i) → (∀ i, (M i : ℝ) ≤ K*X^ζ) →
      ∀ i, (q_31 n d A h e B M (fun k => ⌊ξ*(B k).card⌋₊) q i : ℝ) ≤
        C i*X^(ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ))) := by
  classical
  let F := fun i : Fin r => q_27 (d i.val) h (q_4 n d A h e i.val) *
    q_19 n A h (q_12 (d i.val) h (q_4 n d A h e i.val))
  let m := fun i : Fin r => q i*U i+n*⌊ξ*U i⌋₊
  let C := fun i : Fin r => max 1 ((2:ℝ)^(U i)*(((q_4 n d A h e i.val+1:ℕ):ℝ)^n)^(U i)*
    K^(m i)*(F i:ℝ))
  refine ⟨C,fun i => le_max_left _ _,?_⟩
  intro X ζ hX hζ B M hU hM i
  have hxc : 1 ≤ K*X^ζ := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX hζ)
  have hm : q i*(B i).card+n*⌊ξ*(B i).card⌋₊ ≤ m i := by
    apply Nat.add_le_add (Nat.mul_le_mul_left _ (hU i))
    apply Nat.mul_le_mul_left
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hU i) hξ
  have hpow : (M i:ℝ)^(q i*(B i).card+n*⌊ξ*(B i).card⌋₊) ≤ (K*X^ζ)^(m i) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (hM i) _).trans (pow_le_pow_right₀ hxc hm)
  have he : ζ*(m i:ℝ) ≤ ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ)) := by
    have hh := Nat.floor_le (mul_nonneg hξ (Nat.cast_nonneg (U i)))
    dsimp only [m]
    push_cast
    apply mul_le_mul_of_nonneg_left _ hζ
    calc
      _ ≤ (q i:ℝ)*U i+n*(ξ*U i) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n))
      _ = _ := by ring
  have hdeg : 1 ≤ ((q_4 n d A h e i.val+1:ℕ):ℝ)^n := by
    apply one_le_pow₀
    exact_mod_cast Nat.le_add_left 1 _
  calc
    _ = (2:ℝ)^(B i).card * (((q_4 n d A h e i.val+1:ℕ):ℝ)^n)^(B i).card *
      (M i:ℝ)^(q i*(B i).card+n*⌊ξ*(B i).card⌋₊) * (F i:ℝ) := by
        simp only [q_31,F,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    _ ≤ (2:ℝ)^(U i) * (((q_4 n d A h e i.val+1:ℕ):ℝ)^n)^(U i) *
      (K*X^ζ)^(m i) * (F i:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul _ hpow (pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (hU i))
          (pow_le_pow_right₀ hdeg (hU i)) (by positivity) (by positivity)
    _ = ((2:ℝ)^(U i) * (((q_4 n d A h e i.val+1:ℕ):ℝ)^n)^(U i) *
      K^(m i)*(F i:ℝ))*X^(ζ*(m i:ℝ)) := by
        rw [mul_pow,← Real.rpow_mul_natCast (zero_le_one.trans hX)]
        ring
    _ ≤ C i*X^(ζ*(m i:ℝ)) := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX he)
      ((le_max_left _ _ : (1:ℝ) ≤ C i).trans' zero_le_one)
theorem q_318 {r : ℕ} (L : ℕ) (b : Fin r → ℕ)
    (C κ : Fin r → ℝ) (hC : ∀ i, 1 ≤ C i) (hκ : ∀ i, 0 ≤ κ i)
    (X : ℝ) (hX : 1 ≤ X) (hb : ∀ i, (b i : ℝ) ≤ C i*X^(κ i)) :
    ((∑ i ∈ Finset.range (r+1), L * ∏ j ∈ Finset.range i,
      if hj : j < r then b ⟨j,hj⟩ else 1 : ℕ):ℝ) ≤
      (r+1:ℕ)*(L:ℝ)*(∏ j, C j)*X^(∑ j, κ j) := by
  classical
  let F : ℕ → ℝ := fun j => if hj : j < r then C ⟨j,hj⟩*X^(κ ⟨j,hj⟩) else 1
  have hF : ∀ j, 1 ≤ F j := by
    intro j
    dsimp only [F]
    split_ifs with hj
    · exact one_le_mul_of_one_le_of_one_le (hC ⟨j,hj⟩) (Real.one_le_rpow hX (hκ ⟨j,hj⟩))
    · rfl
  have hprod (i : ℕ) (hi : i ≤ r) :
      ((∏ j ∈ Finset.range i, if hj : j < r then b ⟨j,hj⟩ else 1 : ℕ):ℝ) ≤
        (∏ j, C j)*X^(∑ j, κ j) := by
    calc
      _ ≤ ∏ j ∈ Finset.range i, F j := by
        rw [Nat.cast_prod]
        apply Finset.prod_le_prod
        · intro j _; exact Nat.cast_nonneg _
        · intro j _
          dsimp only [F]
          split_ifs with hj
          · exact hb ⟨j,hj⟩
          · norm_num
      _ ≤ ∏ j ∈ Finset.range r, F j :=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hi)
          (fun j _ => zero_le_one.trans (hF j)) (fun j _ _ => hF j)
      _ = ∏ j : Fin r, C j*X^(κ j) := by
        rw [← Fin.prod_univ_eq_prod_range]
        simp [F]
      _ = _ := by rw [Finset.prod_mul_distrib,Real.rpow_sum_of_pos (zero_lt_one.trans_le hX)]
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _i ∈ Finset.range (r+1), (L:ℝ)*((∏ j, C j)*X^(∑ j, κ j)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left (hprod i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
end QuarticPowerFree
end OAI
end
section
namespace OAI
open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree
section
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
theorem q_284 (n r E A h e : ℕ) (hr : 0 < r) (d : ℕ → ℕ)
    (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (γ ξ w : ℝ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (hw : 0 ≤ w) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ U : Fin r → ℕ, (∀ i, ζ*(U i:ℝ) ≤ a i+2*γ) ∧
    ∃ K X₀ : ℝ, 1 ≤ K ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
      ∀ (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × q_1 n),
      (∀ z, q_29 G h e z.val (start z)) →
    ∃ B : Fin r → Finset ℕ,
      (∀ i, (B i).card ≤ U i ∧ a i+γ ≤ ζ*((B i).card:ℝ)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i p, p ∈ B i → p.Prime ∧ X^ζ ≤ (p:ℝ) ∧ (p:ℝ) ≤ K*X^ζ) ∧
      (G.points.card:ℝ)/2 ≤ (Finset.univ.filter
        (q_54 (E := E) G d A h e r start B ξ)).card := by
  classical
  obtain ⟨C,hC,b,hblocks⟩ := q_405 n d A h e r E
  let η := ξ/(4*r)
  have hη : 0 < η := div_pos hξ (by exact_mod_cast (show 0 < 4*r by omega))
  let V : ℕ := ((E+n).choose n+1)^r
  obtain ⟨T,hTlarge⟩ := exists_nat_gt (2*(V:ℝ)/η)
  have hT : 0 < T := by
    have : (0:ℝ) < T := lt_of_le_of_lt (div_nonneg (by positivity) hη.le) hTlarge
    exact_mod_cast this
  have hVT : (V:ℝ)/T ≤ η/2 := by
    have htc : (0:ℝ) < T := by exact_mod_cast hT
    apply (div_le_iff₀ htc).mpr
    have hh := (div_lt_iff₀ hη).mp hTlarge
    nlinarith
  let ζ := γ/((T:ℝ)+1)
  have hζ : 0 < ζ := div_pos hγ (by positivity)
  have hζT : ζ*T ≤ γ := by
    have he : ζ*((T:ℝ)+1) = γ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let ell := fun i => ⌊(a i+γ)/ζ⌋₊
  let U := fun i => ell i+T
  have hU (i) : ζ*(U i:ℝ) ≤ a i+2*γ :=
    (q_285 (a i) γ ζ T (U i) (ha i) hγ hζ hζT (by dsimp [U,ell]; omega) le_rfl).2
  let v : ℕ := ⌊((w*b+1)*(r+1:ℕ))/ζ⌋₊
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(v:ℝ)/η)
  let t : ℕ := (∑ i, ell i)+T+N+1
  have hsize (i) : ell i+T < t := by
    have he : ell i ≤ ∑ j, ell j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [t]
    omega
  have hbound (i) : (v:ℝ)/((t:ℝ)-(ell i+T)) ≤ η/2 := by
    have hp : (0:ℝ) < (t:ℝ)-(ell i+T) := by
      have hh : (ell i:ℝ)+T < t := by exact_mod_cast hsize i
      linarith
    have he : (ell i:ℝ) ≤ ∑ j, (ell j:ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    have ht : (t:ℝ) = (∑ j, (ell j:ℝ))+T+N+1 := by simp [t]
    have hn := (div_lt_iff₀ hη).mp hN
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨ζ,hζ,U,hU,2^(r*t+1),max 1 C,one_le_pow₀ (by norm_num),?_⟩
  intro X hX G hheight start hs
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hCX : C ≤ X := (le_max_right _ _).trans hX.le
  have hxζ : 1 ≤ X^ζ := Real.one_le_rpow hX1.le hζ.le
  obtain ⟨P,hPcard,hPdisj,hP⟩ := q_462 r t (X^ζ) hxζ
  obtain ⟨B,hB,hreg⟩ := hblocks G start hs r P ell T X ζ w η ξ hX1 hCX hw hheight hζ hξ
    (fun i p hp => (hP i p hp).1) (fun i p hp => (hP i p hp).2.1) hT
    (fun i => by rw [hPcard]; exact hsize i)
    (fun i => by rw [hPcard]; exact add_le_add hVT (hbound i) |>.trans_eq (by ring))
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i
    refine ⟨(hB i).2.2,?_⟩
    exact (q_285 (a i) γ ζ T (B i).card (ha i) hγ hζ hζT
      (hB i).2.1 (hB i).2.2).1
  · intro i j hij
    exact (hPdisj i j hij).mono (hB i).1 (hB j).1
  · intro i p hp
    exact hP i p ((hB i).1 hp)
  · have he : 1-(r:ℝ)*η/ξ = 3/4 := by
      dsimp only [η]
      have hrc : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
      ring
    change (G.points.card:ℝ)/2 ≤ _
    have hr' : (3/4:ℝ)*G.points.card ≤
        (Finset.univ.filter (q_54 (E := E) G d A h e r start B ξ)).card := by
      unfold q_54 q_96
      rw [he] at hreg
      convert hreg using 1
      congr 1
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith [show (0:ℝ) ≤ G.points.card from Nat.cast_nonneg _]
end
open scoped BigOperators
theorem q_358 {r : ℕ} (n : ℕ) (a : Fin r → ℝ) (q : Fin r → ℕ)
    (ha : ∀ i, 0 ≤ a i) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ ξ : ℝ, 0 < γ ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      ξ*((∑ i, a i)+(r:ℝ)*γ) ≤ γ/2 ∧
      (∑ i, (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ)) ≤ (∑ i, (q i:ℝ)*a i)+ε/2 := by
  classical
  let A := ∑ i, a i
  let Q := ∑ i, (q i:ℝ)
  let B := 2*Q+n*A+2*(n:ℝ)*r+1
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hB : 0 < B := by dsimp only [B]; positivity
  let γ := min 1 (ε/(4*B))
  have hγ : 0 < γ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγB : γ*B ≤ ε/4 := by
    have hh : γ ≤ ε/(4*B) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*B)).mp hh
    linarith
  let D := A+(r:ℝ)*γ+1
  have hD : 0 < D := by dsimp only [D]; positivity
  let ξ := min γ (γ/(4*D))
  have hξ : 0 < ξ := lt_min hγ (div_pos hγ (by positivity))
  have hξγ : ξ ≤ γ := min_le_left _ _
  have hξ1 : ξ ≤ 1 := hξγ.trans hγ1
  have hξD : ξ*D ≤ γ/4 := by
    have hh : ξ ≤ γ/(4*D) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*D)).mp hh
    linarith
  refine ⟨γ,ξ,hγ,hξ,hξ1,?_,?_⟩
  · change ξ*(A+(r:ℝ)*γ) ≤ γ/2
    dsimp only [D] at hξD
    nlinarith
  · have he : (∑ i, (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ)) =
        (∑ i, (q i:ℝ)*a i)+2*γ*Q+(n:ℝ)*ξ*A+2*γ*(n:ℝ)*ξ*r := by
      calc
        _ = ∑ i, ((q i:ℝ)*a i+2*γ*(q i:ℝ)+(n:ℝ)*ξ*a i+2*γ*(n:ℝ)*ξ) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, A, Q]
          ring
    have ha' : (n:ℝ)*ξ*A ≤ (n:ℝ)*γ*A := by gcongr
    have hr' : 2*γ*(n:ℝ)*ξ*r ≤ 2*γ*(n:ℝ)*r := by
      calc
        _ ≤ 2*γ*(n:ℝ)*1*r := by gcongr
        _ = _ := by ring
    rw [he]
    dsimp only [B] at hγB
    nlinarith
open MvPolynomial
open scoped BigOperators Classical
open scoped Classical
theorem q_443 (n r A e₀ : ℕ) (hr : 0 < r)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (Cbox w : ℝ) (hCbox : 1 ≤ Cbox) (hw : 0 ≤ w)
    (a δ : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hδ : ∀ i, 0 < δ i)
    (hprefix : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j)
    (ε : ℝ) (hε : 0 < ε) (c Kex : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (hKex : ∀ e, 1 ≤ Kex e) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
        (∀ z ∈ G.points, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
        q_0 I ≤ r → q_16 I ≤ e₀ →
        (∀ z ∈ G.points, q_64 I z) →
        (∀ (i : Fin r) (e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
          I ≤ J → q_103 J G.points A → q_16 J ≤ e →
          q_0 J = r-i.val → (∃ z ∈ G.points, q_64 J z) →
          ((G.points.filter (q_64 J)).card:ℝ) ≤ Kex e*X^(ε/4) ∨
          ∀ T : ℝ, 1 ≤ T → T^(r-i.val) / (((r-i.val).factorial:ℝ)*(δ i)^(r-i.val)) -
            c e*T^(r-i.val-1) ≤ q_32 J ω T) →
        (G.points.card:ℝ) ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
  classical
  let q := fun i : Fin r => r-i.val
  obtain ⟨γ,ξ,hγ,hξ,hξ1,hloss,hexponent⟩ := q_358 n a q ha ε hε
  choose D Xcut hcut using fun (i : Fin r) (e : ℕ) => q_357 ω hω
    (q i) (by dsimp [q]; omega) (δ i) (γ/2) (c e) Cbox (hδ i) (by linarith) (hc e) hCbox
  let chooseD : ℕ → ℕ → ℕ := fun i e => if hi : i < r then D ⟨i,hi⟩ e else 1
  let e := q_36 n A r e₀
  obtain ⟨d,E,hd⟩ := q_373 n A r e r chooseD
  let ed := fun i : Fin r => q_4 n d A r e i.val
  have hd' (i : Fin r) : D i (ed i) ≤ d i.val ∧ d i.val ≤ E := by
    have hh := hd i.val i.isLt
    refine ⟨?_,hh.2⟩
    simpa only [chooseD,dif_pos i.isLt,ed] using hh.1.ge
  obtain ⟨ζ,hζ,U,hUwidth,K,Xpool,hK,hblocks⟩ :=
    q_284 n r E A r e hr d a ha γ ξ w hγ hξ hw
  obtain ⟨Cb,hCb,hbranch⟩ := q_300 n d A r e U q (K+1) ξ
    (by linarith) hξ.le
  let Ke := 1+∑ i, Kex (ed i)
  have hKe : 1 ≤ Ke := by
    dsimp only [Ke]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => zero_le_one.trans (hKex (ed i)))]
  have hKei (i) : Kex (ed i) ≤ Ke := by
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hKex (ed j))) (Finset.mem_univ i)
    dsimp only [Ke]
    linarith
  let Lmax := q_19 n A r e₀
  have hCbprod : 0 ≤ ∏ i, Cb i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hCb i))
  let C := 2*((r+1:ℕ):ℝ)*(Lmax+1)*(∏ i, Cb i)*(Ke+1)
  have hC : 0 < C := by
    dsimp only [C]
    have hp : 0 < ∏ i, Cb i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hCb i))
    positivity
  refine ⟨C,max (max 2 Xpool) (∑ i, |Xcut i (ed i)|),hC,?_⟩
  intro X hX G hheight hbox I hI hdim hdeg hG hAlt
  let : I.IsPrime := hI
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hXp : Xpool < X := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX
  have hXc (i : Fin r) : Xcut i (ed i) < X := lt_of_le_of_lt
    ((le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (Xcut j (ed j)))
      (Finset.mem_univ i)).trans (le_max_right _ _))) hX
  obtain ⟨L,hL,start,hs⟩ := q_371 G A r e₀ I hdim hdeg hG
  have hs' : ∀ z, q_29 G r e z.val (start z) := fun z => (hs z).2.1
  obtain ⟨B,hB,hdisj,hprime,hhalf⟩ := hblocks X hXp G hheight start hs'
  let M : Fin r → ℕ := fun _ => ⌈K*X^ζ⌉₊
  have hMx : 1 ≤ K*X^ζ := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX1 hζ.le)
  have hM (i) : 1 ≤ M i := by
    have hh := (Nat.le_ceil (K*X^ζ)).trans' hMx
    exact_mod_cast hh
  have hMp (i) (p : ℕ) (hp : p ∈ B i) : p ≤ M i := by
    have hh := (hprime i p hp).2.2.trans (Nat.le_ceil (K*X^ζ))
    exact_mod_cast hh
  have hMb (i) : (M i:ℝ) ≤ (K+1)*X^ζ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ K*X^ζ by linarith)
    have hx := Real.one_le_rpow hX1 hζ.le
    dsimp only [M]
    nlinarith
  let T := ⌈Ke*X^(ε/4)⌉₊
  have hTx : 1 ≤ Ke*X^(ε/4) := one_le_mul_of_one_le_of_one_le hKe
    (Real.one_le_rpow hX1 (by linarith))
  have hT : 1 ≤ T := by
    have hh := hTx.trans (Nat.le_ceil (Ke*X^(ε/4)))
    exact_mod_cast hh
  have hTb : (T:ℝ) ≤ (Ke+1)*X^(ε/4) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ Ke*X^(ε/4) by linarith)
    have hx := Real.one_le_rpow hX1 (show 0 ≤ ε/4 by linarith)
    dsimp only [T]
    nlinarith
  let Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop := fun _ J =>
    (G.points.filter (q_64 J)).card ≤ T
  have hmargin := q_327 a δ (fun i => (B i).card) γ ζ ξ ha hγ hξ.le hξ1
    hloss (fun i => (hB i).2) hprefix
  have hdesc (i : ℕ) (hi : i < r) (z : G.points)
      (hz : q_54 (E := E) G d A r e r start B ξ z)
      (hne : ¬ Ex i (q_2 (E := E) G d A r e start B i z).1)
      (hdi : q_0 (q_2 (E := E) G d A r e start B i z).1 = r-i) :
      q_0 (q_2 (E := E) G d A r e start B (i+1) z).1 <
        q_0 (q_2 (E := E) G d A r e start B i z).1 := by
    let ii : Fin r := ⟨i,hi⟩
    let s := q_2 (E := E) G d A r e start B i z
    have hstate := q_30 (E := E) G d A r e start hs' B i z
    have hcontext := q_407 (E := E) G d A r e start hs' B I
      (fun z => ⟨(hs z).2.2.1,(hs z).2.2.2⟩) i z
    have hH : ∀ T' : ℝ, 1 ≤ T' → T'^(q ii)/(((q ii).factorial:ℝ)*(δ ii)^(q ii)) -
        c (ed ii)*T'^(q ii-1) ≤ q_32 s.1 ω T' := by
      rcases hAlt ii (ed ii) s.1 hstate.1.1 hcontext.1 hcontext.2 hstate.1.2.2 hdi
        ⟨z.val,z.property,hstate.2.2.2.1⟩ with hsmall | hH
      · apply False.elim
        apply hne
        have hh : ((G.points.filter (q_64 s.1)).card:ℝ) ≤ (T:ℝ) := hsmall.trans
          ((mul_le_mul_of_nonneg_right (hKei ii) (Real.rpow_nonneg hXpos.le _)).trans (Nat.le_ceil _))
        exact_mod_cast hh
      · exact hH
    let Q := (q_9 B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ eval z.val s.2.minor)
    have hprod : X^(δ ii+γ/2) ≤ ∏ p ∈ Q, (p:ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hX1 (hmargin ii)).trans
        (q_272 B hdisj i (eval z.val s.2.minor) X ζ ξ hX1 hζ.le
          (fun j p hp => (hprime j p hp).2.1)
          (fun j => q_54.bad_minor G d A r e r start B ξ z hz i hi.le j))
    rw [q_89]
    apply hcut ii (ed ii) X (hXc ii) r E G d A r e i (hd' ii).1 (hd' ii).2 hbox
      z.val z.property s hstate hdi hH B Q (Finset.filter_subset _ _)
    · intro p hp
      obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
      exact (hprime j p hpj).1
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · exact hprod
  have hcount := q_422 G d A r e start hs' B M ξ hξ.le L T Ex
    (fun z => (hs z).1) hT (fun z => (hs' z).1.2.1) hM
    (fun i p hp => (hprime i p hp).1) hMp hhalf hdesc (fun _ _ _ hh => hh)
  let κ := fun i : Fin r => ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ))
  have hκ (i) : 0 ≤ κ i := by dsimp [κ]; positivity
  have hsum : ∑ i, κ i ≤ (∑ i, (q i:ℝ)*a i)+ε/2 := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hexponent
    dsimp only [κ]
    calc
      _ = (ζ*(U i:ℝ))*((q i:ℝ)+(n:ℝ)*ξ) := by ring
      _ ≤ (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ) :=
        mul_le_mul_of_nonneg_right (hUwidth i) (by positivity)
  have hforest := q_318 L.length
    (q_31 n d A r e B M (fun k => ⌊ξ*(B k).card⌋₊) q)
    Cb κ hCb hκ X hX1 (hbranch X ζ hX1 hζ.le B M (fun i => (hB i).1) hMb)
  have hcount' : (G.points.card:ℝ) ≤ 2*((r+1:ℕ):ℝ)*L.length*(∏ i, Cb i)*
      X^(∑ i, κ i)*((Ke+1)*X^(ε/4)) := by
    have hh : (G.points.card:ℝ) ≤ 2*((∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then q_31 n d A r e B M
        (fun k => ⌊ξ*(B k).card⌋₊) q ⟨j,hj⟩ else 1 : ℕ):ℝ)*(T:ℝ) := by
      exact_mod_cast hcount
    apply hh.trans
    have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hforest (by norm_num : (0:ℝ) ≤ 2)) hTb
      (Nat.cast_nonneg T) (by positivity)
    convert hh' using 1; ring
  calc
    (G.points.card:ℝ) ≤ 2*((r+1:ℕ):ℝ)*L.length*(∏ i, Cb i)*(Ke+1)*X^((∑ i, κ i)+ε/4) := by
      rw [Real.rpow_add hXpos]
      convert hcount' using 1; ring
    _ ≤ C*X^((∑ i, κ i)+ε/4) := by
      have hL' : (L.length:ℝ) ≤ (Lmax:ℝ)+1 := by exact_mod_cast (hL.trans (Nat.le_succ Lmax))
      dsimp only [C]
      gcongr
    _ ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 ?_) hC.le
      dsimp only [q] at hsum
      linarith
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
section
open scoped BigOperators
def q_114 (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1)).biUnion Finset.HasAntidiagonal.antidiagonal
@[simp] theorem mem_simplexPairs (x : ℕ × ℕ) (N : ℕ) :
    x ∈ q_114 N ↔ x.1+x.2 ≤ N := by
  simp only [q_114, Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro h; exact ⟨_, by omega, rfl⟩
theorem q_398 (N : ℕ) :
    2*(q_114 N).card = (N+1)*(N+2) := by
  rw [q_114, Finset.card_biUnion]
  · simp_rw [Finset.Nat.card_antidiagonal]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      nlinarith
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.HasAntidiagonal.mem_antidiagonal.mp hi).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.mp hj))
def q_14 (a b T : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (T+1)) ×ˢ (Finset.range (T+1))).filter
    (fun x => a*x.1+b*x.2 ≤ T)
theorem q_72 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x : ℕ × ℕ) (T : ℕ) :
    x ∈ q_14 a b T ↔ a*x.1+b*x.2 ≤ T := by
  simp only [q_14, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x.1 ≤ a*x.1 := by nlinarith
    have hy : x.2 ≤ b*x.2 := by nlinarith
    exact ⟨⟨by omega, by omega⟩, h⟩
private theorem q_445 (a b : ℕ) :
    Function.Injective (fun x : ℕ × ℕ => ((x.1/b,x.2/a),(x.1%b,x.2%a))) := by
  intro x y h
  have hq := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  have hr1 := congrArg Prod.fst hr
  have hr2 := congrArg Prod.snd hr
  apply Prod.ext
  · have hx := Nat.mod_add_div x.1 b
    have hy := Nat.mod_add_div y.1 b
    dsimp at hq1 hr1
    rw [hq1, hr1] at hx
    omega
  · have hx := Nat.mod_add_div x.2 a
    have hy := Nat.mod_add_div y.2 a
    dsimp at hq2 hr2
    rw [hq2, hr2] at hx
    omega
theorem q_467 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (T : ℕ) :
    (q_14 a b T).card ≤
      (q_114 (T/(a*b))).card * (a*b) := by
  let f := fun x : ℕ × ℕ => ((x.1/b,x.2/a),(x.1%b,x.2%a))
  have hin (x : ℕ × ℕ) (hx : x ∈ q_14 a b T) :
      f x ∈ (q_114 (T/(a*b))) ×ˢ
        ((Finset.range b) ×ˢ (Finset.range a)) := by
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · apply (mem_simplexPairs _ _).mpr
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < a*b)).mpr
      have h := (q_72 ha hb x T).mp hx
      have hx1 := Nat.div_mul_le_self x.1 b
      have hx2 := Nat.div_mul_le_self x.2 a
      dsimp [f]
      nlinarith [Nat.mul_le_mul_left a hx1, Nat.mul_le_mul_left b hx2]
    · simp [f, Nat.mod_lt _ ha, Nat.mod_lt _ hb]
  have h := Finset.card_le_card_of_injOn f hin
    (fun _ _ _ _ he => q_445 a b he)
  simpa [Finset.card_product, mul_comm a b] using h
theorem q_468 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T N : ℕ) (hTN : a*b*(N+2) ≤ T) :
    (q_114 N).card * (a*b) ≤ (q_14 a b T).card := by
  let S := (q_114 N) ×ˢ ((Finset.range b) ×ˢ (Finset.range a))
  let f := fun x : (ℕ × ℕ) × (ℕ × ℕ) => (b*x.1.1+x.2.1,a*x.1.2+x.2.2)
  have hin (x : (ℕ × ℕ) × (ℕ × ℕ)) (hx : x ∈ S) :
      f x ∈ q_14 a b T := by
    rcases Finset.mem_product.mp hx with ⟨hn, hr⟩
    have hn' := (mem_simplexPairs _ _).mp hn
    rcases Finset.mem_product.mp hr with ⟨hr1, hr2⟩
    have hr1' := Finset.mem_range.mp hr1
    have hr2' := Finset.mem_range.mp hr2
    apply (q_72 ha hb _ T).mpr
    dsimp [f]
    nlinarith [Nat.mul_le_mul_left (a*b) hn', Nat.mul_le_mul_left a (Nat.le_of_lt hr1'),
      Nat.mul_le_mul_left b (Nat.le_of_lt hr2')]
  have hinj : Set.InjOn f (S : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    intro x hx y hy he
    have hx' := Finset.mem_product.mp (Finset.mem_product.mp hx).2
    have hy' := Finset.mem_product.mp (Finset.mem_product.mp hy).2
    have hleft := congrArg Prod.fst he
    have hright := congrArg Prod.snd he
    have hm1 := congrArg (fun n => n % b) hleft
    have hm2 := congrArg (fun n => n % a) hright
    dsimp [f] at hleft hright hm1 hm2
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx'.1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hy'.1)] at hm1
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx'.2),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hy'.2)] at hm2
    apply Prod.ext
    · apply Prod.ext <;> nlinarith
    · exact Prod.ext hm1 hm2
  have h := Finset.card_le_card_of_injOn f hin hinj
  simpa [S, Finset.card_product, mul_comm a b] using h
end
theorem q_234 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T : ℕ) :
    T^2 ≤ 2*(a*b)*(q_14 a b T).card + 3*(a*b)*T + 7*(a*b)^2 ∧
    2*(a*b)*(q_14 a b T).card ≤ T^2 + 3*(a*b)*T + 2*(a*b)^2 := by
  let L := a*b
  let q := T/L
  have hL : 0 < L := Nat.mul_pos ha hb
  have hq : L*q ≤ T := by
    dsimp [q]
    nlinarith [Nat.div_mul_le_self T L]
  have hT : T ≤ L*(q+1) := by
    have hr := Nat.mod_lt T hL
    have hm := Nat.mod_add_div T L
    dsimp [q]
    nlinarith
  constructor
  · by_cases hq2 : 2 ≤ q
    · let N := q-2
      have hN : q = N+2 := by omega
      have hTN : a*b*(N+2) ≤ T := by simpa only [L, ← hN] using hq
      have hl := q_468 ha hb T N hTN
      have hc := q_398 N
      have h0 : L*(N+1)*(N+2) ≤ 2*(q_14 a b T).card := by
        dsimp [L]
        nlinarith [Nat.mul_le_mul_left 2 hl]
      have h1 := Nat.mul_le_mul_left L h0
      have h2 : T^2 ≤ (L*(N+3))^2 := by
        exact Nat.pow_le_pow_left (by nlinarith [hT]) 2
      have h3 : L*N ≤ T := by nlinarith [hq]
      have h4 := Nat.mul_le_mul_left (3*L) h3
      change T^2 ≤ 2*L*(q_14 a b T).card + 3*L*T+7*L^2
      nlinarith
    · have hsmall : T ≤ 2*L := by nlinarith [hT]
      have hsquare := Nat.pow_le_pow_left hsmall 2
      change T^2 ≤ 2*L*(q_14 a b T).card + 3*L*T+7*L^2
      nlinarith
  · have hu := q_467 ha hb T
    have hc := q_398 q
    have h0 : 2*(q_14 a b T).card ≤ (q+1)*(q+2)*L := by
      change (q_14 a b T).card ≤ (q_114 q).card * L at hu
      nlinarith [Nat.mul_le_mul_left 2 hu]
    have h1 := Nat.mul_le_mul_left L h0
    have hprod := Nat.mul_le_mul (Nat.add_le_add_right hq L)
      (Nat.add_le_add_right hq (2*L))
    change 2*L*(q_14 a b T).card ≤ T^2+3*L*T+2*L^2
    nlinarith
theorem q_314 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (T : ℕ) :
    |((q_14 a b T).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| ≤
      3/2*(T:ℝ) + 7/2*(a*b : ℕ) := by
  have hL : (0:ℝ) < (a*b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  have ⟨hlo, hhi⟩ := q_234 ha hb T
  have hlo' : (T:ℝ)^2 ≤ 2*(a*b : ℕ)*(q_14 a b T).card +
      3*(a*b : ℕ)*T+7*(a*b : ℕ)^2 := by exact_mod_cast hlo
  have hhi' : 2*(a*b : ℕ)*(q_14 a b T).card ≤ (T:ℝ)^2 +
      3*(a*b : ℕ)*T+2*(a*b : ℕ)^2 := by exact_mod_cast hhi
  have hden : (0:ℝ) < 2*(a*b : ℕ) := by positivity
  have heq := div_mul_cancel₀ ((T:ℝ)^2) (ne_of_gt hden)
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith [sq_nonneg (a*b : ℕ)]
abbrev NatTriple := ℕ × ℕ × ℕ
def q_10 (a b c : ℕ) (x : NatTriple) : ℕ := a*x.1+b*x.2.1+c*x.2.2
def q_58 (a b c T : ℕ) : Finset NatTriple :=
  ((Finset.range (T+1)) ×ˢ (Finset.range (T+1)) ×ˢ (Finset.range (T+1))).filter
    (fun x => q_10 a b c x ≤ T)
theorem q_187 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : NatTriple) (T : ℕ) : x ∈ q_58 a b c T ↔ q_10 a b c x ≤ T := by
  simp only [q_58, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x.1 ≤ a*x.1 := by nlinarith
    have hy : x.2.1 ≤ b*x.2.1 := by nlinarith
    have hz : x.2.2 ≤ c*x.2.2 := by nlinarith
    dsimp [q_10] at h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩
def q_170 (m x : NatTriple) : Prop := m.1 ≤ x.1 ∧ m.2.1 ≤ x.2.1 ∧ m.2.2 ≤ x.2.2
instance (m x : NatTriple) : Decidable (q_170 m x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def q_113 (a b c : ℕ) (m : NatTriple) (T : ℕ) : Finset NatTriple :=
  (q_58 a b c T).filter (fun x => ¬ q_170 m x)
def q_478 (m : NatTriple) : NatTriple ↪ NatTriple where
  toFun x := (m.1+x.1,m.2.1+x.2.1,m.2.2+x.2.2)
  inj' := by
    intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x : NatTriple => x.2.1) h
    have h3 := congrArg (fun x : NatTriple => x.2.2) h
    simp only [Nat.add_left_cancel_iff] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
theorem q_352 (a b c : ℕ) (m x : NatTriple) :
    q_10 a b c (q_478 m x) = q_10 a b c m + q_10 a b c x := by
  change a*(m.1+x.1)+b*(m.2.1+x.2.1)+c*(m.2.2+x.2.2) = _
  dsimp [q_10]
  ring
theorem q_400 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : q_10 a b c m ≤ T) :
    (q_113 a b c m T).card +
      (q_58 a b c (T-q_10 a b c m)).card = (q_58 a b c T).card := by
  have he : (q_58 a b c T).filter (q_170 m) =
      (q_58 a b c (T-q_10 a b c m)).map (q_478 m) := by
    ext x
    simp only [Finset.mem_filter, q_187 ha hb hc, Finset.mem_map]
    constructor
    · rintro ⟨hx, hm⟩
      let y : NatTriple := (x.1-m.1,x.2.1-m.2.1,x.2.2-m.2.2)
      have hy : q_478 m y = x := by
        rcases hm with ⟨h1,h2,h3⟩
        change (m.1+(x.1-m.1),m.2.1+(x.2.1-m.2.1),m.2.2+(x.2.2-m.2.2)) = x
        simp [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2, Nat.add_sub_cancel' h3]
      refine ⟨y, ?_, hy⟩
      rw [← hy, q_352] at hx
      omega
    · rintro ⟨y, hy, rfl⟩
      constructor
      · rw [q_352]
        omega
      · change m.1 ≤ m.1+y.1 ∧ m.2.1 ≤ m.2.1+y.2.1 ∧ m.2.2 ≤ m.2.2+y.2.2
        omega
  have hh := Finset.card_filter_add_card_filter_not (s := q_58 a b c T) (p := q_170 m)
  rw [he, Finset.card_map] at hh
  change _ + ((q_58 a b c T).filter (fun x => ¬ q_170 m x)).card = _ at hh
  dsimp [q_113]
  omega
def q_506 (i : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (i,x)
  inj' := by intro x y h; exact congrArg Prod.snd h
def q_500 (u j : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (u+x.1,j,x.2)
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
      (congrArg (fun z : NatTriple => z.2.2) h)
def q_504 (u v k : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (u+x.1,v+x.2,k)
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
      (Nat.add_left_cancel (congrArg (fun z : NatTriple => z.2.1) h))
def q_427 (a b c u T : ℕ) : Finset NatTriple :=
  (Finset.range u).biUnion fun i => (q_14 b c (T-a*i)).map (q_506 i)
def q_354 (a b c u v T : ℕ) : Finset NatTriple :=
  (Finset.range v).biUnion fun j => (q_14 a c (T-(a*u+b*j))).map (q_500 u j)
def q_469 (a b c u v w T : ℕ) : Finset NatTriple :=
  (Finset.range w).biUnion fun k => (q_14 a b (T-(a*u+b*v+c*k))).map (q_504 u v k)
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
section
open scoped BigOperators
@[simp] theorem firstSlab_apply (i : ℕ) (x : ℕ × ℕ) : q_506 i x = (i,x) := rfl
@[simp] theorem secondSlab_apply (u j : ℕ) (x : ℕ × ℕ) : q_500 u j x = (u+x.1,j,x.2) := rfl
@[simp] theorem thirdSlab_apply (u v k : ℕ) (x : ℕ × ℕ) : q_504 u v k x = (u+x.1,v+x.2,k) := rfl
theorem q_379 {a b c u T : ℕ} (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hT : a*u ≤ T) (x : NatTriple) :
    x ∈ q_427 a b c u T ↔ x.1 < u ∧ q_10 a b c x ≤ T := by
  simp only [q_427, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    have hs : a*i ≤ T := (Nat.mul_le_mul_left a (Nat.le_of_lt hi)).trans hT
    have hy' := (q_72 hb hc y (T-a*i)).mp hy
    simp only [firstSlab_apply, q_10]
    exact ⟨hi, by omega⟩
  · rintro ⟨hx, hw⟩
    refine ⟨x.1, hx, (x.2.1,x.2.2), ?_, by simp⟩
    apply (q_72 hb hc _ _).mpr
    dsimp [q_10] at hw
    dsimp
    omega
theorem q_333 {a b c u v T : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hT : a*u+b*v ≤ T) (x : NatTriple) :
    x ∈ q_354 a b c u v T ↔ u ≤ x.1 ∧ x.2.1 < v ∧ q_10 a b c x ≤ T := by
  simp only [q_354, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, y, hy, rfl⟩
    have hs : a*u+b*j ≤ T := by nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hj)]
    have hy' := (q_72 ha hc y _).mp hy
    simp only [secondSlab_apply, q_10]
    refine ⟨by omega, hj, ?_⟩
    nlinarith [Nat.sub_add_cancel hs]
  · rintro ⟨hu, hx, hw⟩
    refine ⟨x.2.1, hx, (x.1-u,x.2.2), ?_, ?_⟩
    · apply (q_72 ha hc _ _).mpr
      dsimp [q_10] at hw
      dsimp
      have he := Nat.sub_add_cancel hu
      have hs : a*u+b*x.2.1 ≤ T := by nlinarith [Nat.mul_le_mul_left a hu]
      nlinarith [Nat.sub_add_cancel hs]
    · simp [Nat.add_sub_cancel' hu]
theorem q_475 {a b c u v w T : ℕ} (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (hT : a*u+b*v+c*w ≤ T) (x : NatTriple) :
    x ∈ q_469 a b c u v w T ↔
      u ≤ x.1 ∧ v ≤ x.2.1 ∧ x.2.2 < w ∧ q_10 a b c x ≤ T := by
  simp only [q_469, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨k, hk, y, hy, rfl⟩
    have hs : a*u+b*v+c*k ≤ T := by nlinarith [Nat.mul_le_mul_left c (Nat.le_of_lt hk)]
    have hy' := (q_72 ha hb y _).mp hy
    simp only [thirdSlab_apply, q_10]
    refine ⟨by omega, by omega, hk, ?_⟩
    nlinarith [Nat.sub_add_cancel hs]
  · rintro ⟨hu, hv, hx, hw⟩
    refine ⟨x.2.2, hx, (x.1-u,x.2.1-v), ?_, ?_⟩
    · apply (q_72 ha hb _ _).mpr
      dsimp [q_10] at hw
      dsimp
      have he := Nat.sub_add_cancel hu
      have he' := Nat.sub_add_cancel hv
      have hs : a*u+b*v+c*x.2.2 ≤ T := by
        nlinarith [Nat.mul_le_mul_left a hu, Nat.mul_le_mul_left b hv]
      nlinarith [Nat.sub_add_cancel hs]
    · simp [Nat.add_sub_cancel' hu, Nat.add_sub_cancel' hv]
private theorem q_250 {α β : Type*} [DecidableEq β]
    (q : ℕ → Finset α) (e : ℕ → α ↪ β) (f : β → ℕ)
    (hf : ∀ i x, f (e i x) = i) (n : ℕ) :
    ((Finset.range n).biUnion fun i => (q i).map (e i)).card = ∑ i ∈ Finset.range n, (q i).card := by
  rw [Finset.card_biUnion]
  · simp
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hz
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hz'
    exact hij ((hf i x).symm.trans ((congrArg f (hx.trans hy.symm)).trans (hf j y)))
theorem q_350 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : q_10 a b c m ≤ T) :
    (q_113 a b c m T).card =
      (∑ i ∈ Finset.range m.1, (q_14 b c (T-a*i)).card) +
      (∑ j ∈ Finset.range m.2.1, (q_14 a c (T-(a*m.1+b*j))).card) +
      (∑ k ∈ Finset.range m.2.2, (q_14 a b (T-(a*m.1+b*m.2.1+c*k))).card) := by
  have h1 : a*m.1 ≤ T := by dsimp [q_10] at hT; omega
  have h2 : a*m.1+b*m.2.1 ≤ T := by dsimp [q_10] at hT; omega
  have he : q_113 a b c m T =
      (q_427 a b c m.1 T ∪ q_354 a b c m.1 m.2.1 T) ∪
        q_469 a b c m.1 m.2.1 m.2.2 T := by
    ext x
    rw [q_113, Finset.mem_filter]
    simp only [q_187 ha hb hc,
      Finset.mem_union, q_379 ha hb hc h1, q_333 ha hb hc h2,
      q_475 ha hb hc hT, q_170]
    omega
  have hd12 : Disjoint (q_427 a b c m.1 T) (q_354 a b c m.1 m.2.1 T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (q_379 ha hb hc h1 x).mp hx
    have hy' := (q_333 ha hb hc h2 x).mp hy
    omega
  have hd3 : Disjoint (q_427 a b c m.1 T ∪ q_354 a b c m.1 m.2.1 T)
      (q_469 a b c m.1 m.2.1 m.2.2 T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hy' := (q_475 ha hb hc hT x).mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx' := (q_379 ha hb hc h1 x).mp hx; omega
    · have hx' := (q_333 ha hb hc h2 x).mp hx; omega
  rw [he, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12]
  congr 2
  · exact q_250 _ q_506 Prod.fst (fun _ _ => rfl) _
  · exact q_250 _ (q_500 m.1) (fun x => x.2.1) (fun _ _ => rfl) _
  · exact q_250 _ (q_504 m.1 m.2.1) (fun x => x.2.2) (fun _ _ => rfl) _
theorem q_207 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (s T : ℕ) (hs : s ≤ T) :
    |((q_14 a b (T-s)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| ≤
      ((s:ℝ)+2)*T + 4*(a*b : ℕ) := by
  have hL : (1:ℝ) ≤ (a*b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  have hd : (0:ℝ) < 2*(a*b : ℕ) := by positivity
  have ht : (T-s : ℕ) + s = T := Nat.sub_add_cancel hs
  have ht' : (T-s : ℕ) + (s:ℝ) = T := by exact_mod_cast ht
  have hp := q_314 ha hb (T-s)
  have hdiff : |((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))-(T:ℝ)^2/(2*(a*b : ℕ))| ≤
      (s:ℝ)*T := by
    have hn : ((T-s : ℕ):ℝ)^2-(T:ℝ)^2 ≤ 0 := by nlinarith
    rw [← sub_div, abs_div, abs_of_nonpos hn, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hx := mul_le_mul_of_nonneg_right hL (show (0:ℝ) ≤ (s:ℝ)*T by positivity)
    nlinarith
  calc
    _ ≤ |((q_14 a b (T-s)).card : ℝ) - ((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))| +
        |((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))-(T:ℝ)^2/(2*(a*b : ℕ))| := abs_sub_le ..
    _ ≤ _ := by nlinarith
theorem q_83 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (n E T : ℕ) (hT : E ≤ T) (q : ℕ → ℕ) (hq : ∀ i < n, q i ≤ E) :
    |((∑ i ∈ Finset.range n, (q_14 a b (T-q i)).card : ℕ) : ℝ) -
      (n:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ))| ≤
      (n:ℝ)*((E:ℝ)+2+4*(a*b : ℕ))*((T:ℝ)+1) := by
  have he : (∑ i ∈ Finset.range n,
      (((q_14 a b (T-q i)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ)))) =
      ((∑ i ∈ Finset.range n, (q_14 a b (T-q i)).card : ℕ) : ℝ) -
      (n:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)) := by
    simp [Finset.sum_sub_distrib, mul_div_assoc]
  rw [← he]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |((q_14 a b (T-q i)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, (((E:ℝ)+2+4*(a*b : ℕ))*((T:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hqi := hq i (Finset.mem_range.mp hi)
      have hqi' : (q i:ℝ) ≤ E := by exact_mod_cast hqi
      have hb' := q_207 ha hb (q i) T (hqi.trans hT)
      have hx := mul_le_mul_of_nonneg_right hqi' (show (0:ℝ) ≤ T by positivity)
      nlinarith
    _ = _ := by simp; ring
noncomputable def q_186 (a b c : ℕ) (m : NatTriple) : ℝ :=
  (m.1:ℝ)*((q_10 a b c m:ℝ)+2+4*(b*c : ℕ)) +
  (m.2.1:ℝ)*((q_10 a b c m:ℝ)+2+4*(a*c : ℕ)) +
  (m.2.2:ℝ)*((q_10 a b c m:ℝ)+2+4*(a*b : ℕ))
theorem q_296 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : q_10 a b c m ≤ T) :
    |((q_113 a b c m T).card : ℝ) -
      (q_10 a b c m : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ))| ≤
      q_186 a b c m * ((T:ℝ)+1) := by
  have h1 := q_83 hb hc m.1 (q_10 a b c m) T hT
    (fun i => a*i) (by intro i hi; dsimp [q_10]; nlinarith [Nat.mul_le_mul_left a (Nat.le_of_lt hi)])
  have h2 := q_83 ha hc m.2.1 (q_10 a b c m) T hT
    (fun j => a*m.1+b*j) (by intro j hj; dsimp [q_10]; nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hj)])
  have h3 := q_83 ha hb m.2.2 (q_10 a b c m) T hT
    (fun k => a*m.1+b*m.2.1+c*k)
    (by intro k hk; dsimp [q_10]; nlinarith [Nat.mul_le_mul_left c (Nat.le_of_lt hk)])
  have he := q_350 ha hb hc m T hT
  have ha' : (a:ℝ) ≠ 0 := by positivity
  have hb' : (b:ℝ) ≠ 0 := by positivity
  have hc' : (c:ℝ) ≠ 0 := by positivity
  have hcoeff : (q_10 a b c m : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ)) =
      (m.1:ℝ)*(T:ℝ)^2/(2*(b*c : ℕ)) + (m.2.1:ℝ)*(T:ℝ)^2/(2*(a*c : ℕ)) +
      (m.2.2:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)) := by
    simp only [q_10, Nat.cast_add, Nat.cast_mul]
    field_simp
  rw [he, Nat.cast_add, Nat.cast_add, hcoeff]
  have habs (x y z u v w : ℝ) : |x+y+z-(u+v+w)| ≤ |x-u|+|y-v|+|z-w| := by
    calc
      _ = |(x-u)+(y-v)+(z-w)| := by congr 1; ring
      _ ≤ |(x-u)+(y-v)|+|z-w| := abs_add_le _ _
      _ ≤ _ := by linarith [abs_add_le (x-u) (y-v)]
  have hh := habs
    (((∑ i ∈ Finset.range m.1, (q_14 b c (T-a*i)).card : ℕ) : ℝ))
    (((∑ j ∈ Finset.range m.2.1, (q_14 a c (T-(a*m.1+b*j))).card : ℕ) : ℝ))
    (((∑ k ∈ Finset.range m.2.2, (q_14 a b (T-(a*m.1+b*m.2.1+c*k))).card : ℕ) : ℝ))
    ((m.1:ℝ)*(T:ℝ)^2/(2*(b*c : ℕ)))
    ((m.2.1:ℝ)*(T:ℝ)^2/(2*(a*c : ℕ)))
    ((m.2.2:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)))
  dsimp [q_186]
  linarith
end
open MvPolynomial
open scoped BigOperators
noncomputable def q_164 {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i => Polynomial.C (X i) * Polynomial.X ^ w i)
theorem q_252 {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    q_164 w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [q_164, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]
theorem q_351 {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) (t : ℕ) :
    (q_164 w p).coeff t = weightedHomogeneousComponent w t p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [q_252, Polynomial.coeff_C_mul_X_pow]
    ext s
    by_cases hs : m = s
    · subst s
      split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial, eq_comm]
    · split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]
theorem q_436 {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) : (q_164 w p).eval 1 = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r => simp [q_252]
  | add p q hp hq => simp [map_add, hp, hq]
theorem q_222 {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    Function.Injective (q_164 (R := R) w) := by
  intro p q h
  simpa only [q_436] using congrArg (Polynomial.eval 1) h
theorem q_131 {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) :
    (q_164 w p).natDegree = weightedTotalDegree w p := by
  classical
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    rw [q_351]
    exact weightedHomogeneousComponent_eq_zero t p ht
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    have hc : (q_164 w p).coeff (Finsupp.weight w m) ≠ 0 := by
      rw [q_351]
      intro he
      have h := congrArg (fun polynomial => polynomial.coeff m) he
      simp [coeff_weightedHomogeneousComponent, mem_support_iff.mp hm] at h
    exact Polynomial.le_natDegree_of_ne_zero hc
theorem q_257 {σ R : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedTotalDegree w (p * q) = weightedTotalDegree w p + weightedTotalDegree w q := by
  rw [← q_131, map_mul, Polynomial.natDegree_mul]
  · rw [q_131, q_131]
  · intro h
    apply hp
    apply q_222 w
    simpa using h
  · intro h
    apply hq
    apply q_222 w
    simpa using h
theorem q_502 {K L M N : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M]
    (g : L →ₗ[K] M) (f : M →ₗ[K] N) (hg : Function.Injective g)
    (he : LinearMap.range g = LinearMap.ker f) :
    Module.finrank K (LinearMap.range f) + Module.finrank K L = Module.finrank K M := by
  rw [← LinearMap.finrank_range_of_inj hg, he]
  exact f.finrank_range_add_finrank_ker
theorem q_339 {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (F G : Submodule K R)
    [Module.Finite K F] (c : R) (hc : c ≠ 0)
    (hdegree : ∀ x : R, c * x ∈ F ↔ x ∈ G) :
    Module.finrank K (F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) +
      Module.finrank K G = Module.finrank K F := by
  let f := (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨c * x.val, (hdegree x.val).mpr x.property⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact mul_left_cancel₀ hc (congrArg Subtype.val h)
  have he : LinearMap.range g = LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (Ideal.Quotient.mk (Ideal.span {c})) (c * y.val) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr ⟨y.val, rfl⟩
    · intro hx
      have hmem : x.val ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
      refine ⟨⟨y, (hdegree y).mp (hy ▸ x.property)⟩, ?_⟩
      apply Subtype.ext
      exact hy.symm
  have hr : LinearMap.range f = F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact q_502 g f hg he
noncomputable def q_62 {σ K : Type*} [CommSemiring K] (w : σ → ℕ) (T : ℕ) :
    Submodule K (MvPolynomial σ K) :=
  restrictSupport K {m | Finsupp.weight w m ≤ T}
theorem q_395 {σ K : Type*} [CommSemiring K] (w : σ → ℕ)
    (T : ℕ) (p : MvPolynomial σ K) :
    p ∈ q_62 w T ↔ weightedTotalDegree w p ≤ T := by
  classical
  simp only [q_62, mem_restrictSupport_iff, weightedTotalDegree,
    Finset.sup_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
theorem q_456 {σ K : Type*} [Finite σ] [CommSemiring K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.Finite K (q_62 (K := K) w T) := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K _)
theorem q_251 {σ K : Type*} [Finite σ] [Field K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.finrank K (q_62 (K := K) w T) =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T} := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)
theorem q_256 {σ K : Type*} [Finite σ] [Field K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (F : MvPolynomial σ K) (hF : F ≠ 0)
    (T : ℕ) (hT : weightedTotalDegree w F ≤ T) :
    Module.finrank K ((q_62 w T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) +
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T - weightedTotalDegree w F} =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T} := by
  have := q_456 (K := K) w hw T
  have hd (p : MvPolynomial σ K) : F * p ∈ q_62 w T ↔
      p ∈ q_62 w (T - weightedTotalDegree w F) := by
    rw [q_395, q_395]
    by_cases hp : p = 0
    · subst p
      simp [weightedTotalDegree]
    · rw [q_257 w F p hF hp]
      omega
  have h := q_339 (q_62 w T)
    (q_62 w (T - weightedTotalDegree w F)) F hF hd
  rwa [q_251 w hw, q_251 w hw] at h
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
open MvPolynomial
noncomputable def q_105 : (Fin 3 →₀ ℕ) ≃ NatTriple :=
  Finsupp.equivFunOnFinite.trans
    { toFun := fun f => (f 0, f 1, f 2)
      invFun := fun x => ![x.1, x.2.1, x.2.2]
      left_inv := by intro f; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨x,y,z⟩; rfl }
def q_15 (a b c : ℕ) : Fin 3 → ℕ := ![a,b,c]
theorem q_224 (a b c : ℕ) (m : Fin 3 →₀ ℕ) :
    Finsupp.weight (q_15 a b c) m = q_10 a b c (q_105 m) := by
  rw [Finsupp.weight_eq_sum]
  simp [Fin.sum_univ_succ, q_15, q_10, q_105, mul_comm, add_assoc]
theorem q_437 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, q_15 a b c i ≠ 0 := by
  intro i
  fin_cases i <;> simp [q_15, ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
theorem q_223 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (T : ℕ) :
    Nat.card {m : Fin 3 →₀ ℕ // Finsupp.weight (q_15 a b c) m ≤ T} =
      (q_58 a b c T).card := by
  let e : {m : Fin 3 →₀ ℕ // Finsupp.weight (q_15 a b c) m ≤ T} ≃
      {x : NatTriple // x ∈ q_58 a b c T} :=
    q_105.subtypeEquiv (by intro m; rw [q_187 ha hb hc, q_224])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
theorem q_199 {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (m : NatTriple)
    (hm : q_10 a b c m = weightedTotalDegree (q_15 a b c) F)
    (T : ℕ) (hT : weightedTotalDegree (q_15 a b c) F ≤ T) :
    Module.finrank K ((q_62 (q_15 a b c) T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) =
      (q_113 a b c m T).card := by
  have hh := q_256 (q_15 a b c)
    (q_437 ha hb hc) F hF T hT
  rw [q_223 ha hb hc, q_223 ha hb hc] at hh
  have hn := q_400 ha hb hc m T (hm ▸ hT)
  rw [hm] at hn
  omega
theorem q_438 {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, weightedTotalDegree (q_15 a b c) F ≤ T →
      |(Module.finrank K ((q_62 (q_15 a b c) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) : ℝ) -
        ((weightedTotalDegree (q_15 a b c) F : ℕ) : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ))|
          ≤ C*((T:ℝ)+1) := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (Finsupp.weight (q_15 a b c))
  have hm' : q_10 a b c (q_105 m) =
      weightedTotalDegree (q_15 a b c) F := by
    rw [← q_224]
    exact hm.symm
  refine ⟨q_186 a b c (q_105 m), by unfold q_186; positivity,
    fun T hT => ?_⟩
  rw [q_199 ha hb hc F hF _ hm' T hT]
  rw [← hm']
  exact q_296 ha hb hc _ T (hm' ▸ hT)
end QuarticPowerFree
open Polynomial Matrix
open scoped BigOperators
namespace QuarticPowerFree.ComplexValues
theorem q_230 (A B : ℤ[X])
    (hB : B.natDegree ≠ 0) {s : ℤ} (hs : B.eval s ∣ A.eval s) :
    B.eval s ∣ A.resultant B := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant A B
    le_rfl le_rfl (Or.inr hB)
  have he := congrArg (Polynomial.eval s) h
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hs _) (dvd_mul_right _ _)
theorem q_488 (B : ℤ[X]) (hB : 0 < B.natDegree)
    (S : Finset ℤ) (q : ℤ) :
    (S.filter (fun s => B.eval s = q)).card ≤ B.natDegree := by
  have hnz : B - C q ≠ 0 := by
    intro hz
    have hh := congrArg Polynomial.natDegree hz
    rw [natDegree_sub_C, natDegree_zero] at hh
    omega
  have hh : (S.filter (fun s => B.eval s = q)).val ⊆ (B - C q).roots := by
    intro s hs
    have he := (Finset.mem_filter.mp hs).2
    exact Polynomial.mem_roots hnz |>.mpr (by simp [he])
  simpa only [natDegree_sub_C] using Polynomial.card_le_degree_of_subset_roots hh
def q_261 (r : ℤ) : Finset ℤ :=
  (r.natAbs.divisors.image (fun n : ℕ => (n : ℤ))) ∪
    (r.natAbs.divisors.image (fun n : ℕ => -(n : ℤ)))
theorem q_484 {r q : ℤ} (hr : r ≠ 0) (hq : q ∣ r) :
    q ∈ q_261 r := by
  have hn : q.natAbs ∈ r.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hq, Int.natAbs_ne_zero.mpr hr⟩
  rcases le_total 0 q with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonneg h]⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonpos h]⟩)
theorem q_432 (r : ℤ) :
    (q_261 r).card ≤ 2 * r.natAbs.divisors.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => (n : ℤ))
    have h₂ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => -(n : ℤ))
    omega)
theorem q_210 (A B : ℤ[X])
    (hB : 0 < B.natDegree) (hres : A.resultant B ≠ 0) (S : Finset ℤ) :
    (S.filter (fun s => B.eval s ∣ A.eval s)).card ≤
      2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by
  classical
  let T := S.filter (fun s => B.eval s ∣ A.eval s)
  have himage : T.image B.eval ⊆ q_261 (A.resultant B) := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    exact q_484 hres (q_230 A B
      (Nat.ne_zero_of_lt hB) (Finset.mem_filter.mp hs).2)
  calc
    T.card = ∑ q ∈ T.image B.eval, (T.filter (fun s => B.eval s = q)).card :=
      (Finset.card_eq_sum_card_image B.eval T)
    _ ≤ ∑ q ∈ T.image B.eval, B.natDegree := by
      apply Finset.sum_le_sum
      intro q _
      exact q_488 B hB T q
    _ = (T.image B.eval).card * B.natDegree := by simp
    _ ≤ (q_261 (A.resultant B)).card * B.natDegree :=
      Nat.mul_le_mul_right _ (Finset.card_le_card himage)
    _ ≤ (2 * (A.resultant B).natAbs.divisors.card) * B.natDegree :=
      Nat.mul_le_mul_right _ (q_432 _)
    _ = 2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by ring
theorem q_85 {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (S : Finset F)
    (hA : A₁.natDegree ≤ A.natDegree) (hB : B₁.natDegree ≤ B.natDegree)
    (hcard : A.natDegree + B.natDegree < S.card)
    (heval : ∀ s ∈ S, A₁.eval s * B.eval s = A.eval s * B₁.eval s) :
    A₁ * B = A * B₁ := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
  · intro s hs
    simpa only [eval_sub, eval_mul, sub_eq_zero] using heval s hs
  · have hd := Polynomial.natDegree_sub_le (A₁ * B) (A * B₁)
    have h₁ := Polynomial.natDegree_mul_le (p := A₁) (q := B)
    have h₂ := Polynomial.natDegree_mul_le (p := A) (q := B₁)
    exact lt_of_le_of_lt (hd.trans (max_le (by omega) (by omega))) hcard
theorem q_82 {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (hB : B₁.natDegree ≤ B.natDegree) (heq : A₁ * B = A * B₁) :
    ∃ c : F, A₁ = C c * A ∧ B₁ = C c * B := by
  have hdvd : B ∣ B₁ := hcop.symm.dvd_of_dvd_mul_left (heq ▸ dvd_mul_left B A₁)
  obtain ⟨Q, hQ⟩ := hdvd
  by_cases hQz : Q = 0
  · refine ⟨0, ?_, ?_⟩
    · have hz : A₁ = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right hBn
        rw [heq, hQ, hQz, mul_zero, mul_zero]
      simpa using hz
    · simp [hQ, hQz]
  · have hdeg : Q.natDegree = 0 := by
      rw [hQ, Polynomial.natDegree_mul hBn hQz] at hB
      omega
    have hQc : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    refine ⟨Q.coeff 0, ?_, ?_⟩
    · apply mul_right_cancel₀ hBn
      conv_lhs => rw [heq, hQ, hQc]
      ring
    · calc B₁ = B * Q := hQ
           _ = B * C (Q.coeff 0) := congrArg (B * ·) hQc
           _ = C (Q.coeff 0) * B := mul_comm _ _
def q_23 {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (i : Option ι) : Fin (a + 1) ⊕ Fin (b + 1) → R :=
  match i with
  | none => Pi.single (Sum.inr ⟨b, Nat.lt_succ_self b⟩) 1
  | some t => Sum.elim (fun j => s t ^ j.val) (fun j => -(v t * s t ^ j.val))
theorem q_172 {R ι : Type*} [CommRing R] [DecidableEq R] {a b : ℕ}
    (s v : ι → R) (t : ι) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    q_23 s v (some t) ⬝ᵥ c =
      (Polynomial.ofFn (a + 1) (fun j => c (Sum.inl j))).eval (s t) -
      v t * (Polynomial.ofFn (b + 1) (fun j => c (Sum.inr j))).eval (s t) := by
  classical
  simp only [q_23, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
theorem q_173 {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    q_23 s v none ⬝ᵥ c = c (Sum.inr ⟨b, Nat.lt_succ_self b⟩) := by
  rw [q_23, single_dotProduct, one_mul]
def q_57 {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    Matrix (Fin (a + 1) ⊕ Fin (b + 1)) (Fin (a + 1) ⊕ Fin (b + 1)) R :=
  Matrix.of (fun j => q_23 s v (e j))
theorem q_226 {F ι : Type*} [Field F] [Fintype ι]
    (A B : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → F) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i) = v i * B.eval (s i))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    (q_57 s v e).det ≠ 0 := by
  classical
  let M := q_57 s v e
  have hker : ∀ c, M *ᵥ c = 0 → c = 0 := by
    intro c hc
    let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
    let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
    have hpdeg : P.natDegree ≤ A.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos A.natDegree)
        (fun j => c (Sum.inl j))
      exact Nat.le_of_lt_succ h
    have hqdeg : Q.natDegree ≤ B.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos B.natDegree)
        (fun j => c (Sum.inr j))
      exact Nat.le_of_lt_succ h
    have hpeval (i : ι) : P.eval (s i) = v i * Q.eval (s i) := by
      have hh := congrFun hc (e.symm (some i))
      change q_23 s v (e (e.symm (some i))) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, q_172] at hh
      exact sub_eq_zero.mp hh
    have hcross : P * B = A * Q := by
      apply q_85 A B P Q (Finset.univ.image s) hpdeg hqdeg
      · simpa only [Finset.card_image_of_injective _ hs, Finset.card_univ] using hcard
      · intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rw [hpeval, heval]
        ring
    obtain ⟨r, hP, hQ⟩ := q_82 A B P Q hcop hBn hqdeg hcross
    have hqzero : Q.coeff B.natDegree = 0 := by
      have hh := congrFun hc (e.symm none)
      change q_23 s v (e (e.symm none)) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, q_173] at hh
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hr : r = 0 := by
      rw [hQ, Polynomial.coeff_C_mul] at hqzero
      exact (mul_eq_zero.mp hqzero).resolve_right (Polynomial.leadingCoeff_ne_zero.mpr hBn)
    have hpzero : P = 0 := by simp [hP, hr]
    have hqzero' : Q = 0 := by simp [hQ, hr]
    funext j
    rcases j with j | j
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hpzero
      simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hqzero'
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
  have hi : Function.Injective (Matrix.mulVecLin M) :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  exact (M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero
theorem q_411 {R S ι : Type*} [CommRing R] [CommRing S]
    {a b : ℕ} (f : R →+* S) (s v : ι → R)
    (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    (q_57 s v e).map f =
      q_57 (fun i => f (s i)) (fun i => f (v i)) e := by
  classical
  ext i j
  change f (q_23 s v (e i) j) = _
  change _ = q_23 (fun i => f (s i)) (fun i => f (v i)) (e i) j
  rcases h : e i with _ | t
  · simp only [q_23]
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hj]
  · rcases j with j | j <;> simp [q_23]
noncomputable def q_97 {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    Fin (a + 1) ⊕ Fin (b + 1) → ℤ := by
  classical
  exact (q_57 s v e).cramer (fun j => if e j = none then 1 else 0)
theorem q_166 {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ A.natDegree ∧ Q.natDegree ≤ B.natDegree ∧
      P = Polynomial.ofFn (A.natDegree + 1)
        (fun j => q_97 s v e (Sum.inl j)) ∧
      Q = Polynomial.ofFn (B.natDegree + 1)
        (fun j => q_97 s v e (Sum.inr j)) := by
  classical
  let M := q_57 s v e
  let u : Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1) → ℤ :=
    fun j => if e j = none then 1 else 0
  let c := M.cramer u
  let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
  let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
  have hdet : M.det ≠ 0 := by
    have h := q_226 A B hcop hBn
      (fun i => (s i : ℂ)) (fun i => (v i : ℂ))
      (Int.cast_injective.comp hs) hcard heval e
    intro hz
    apply h
    have hm := q_411 (Int.castRingHom ℂ) s v e
    simp only [Int.coe_castRingHom] at hm
    rw [← hm, ← Int.cast_det,
      show (q_57 s v e).det = 0 from hz, Int.cast_zero]
  have hc : M *ᵥ c = M.det • u := M.mulVec_cramer u
  have hpdeg : P.natDegree ≤ A.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  have hqdeg : Q.natDegree ≤ B.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  let f := Int.castRingHom ℂ
  have heval' (i : ι) : (P.map f).eval (s i : ℂ) = (v i : ℂ) * (Q.map f).eval (s i : ℂ) := by
    have hh := congrFun hc (e.symm (some i))
    change q_23 s v (e (e.symm (some i))) ⬝ᵥ c = _ at hh
    rw [e.apply_symm_apply, q_172] at hh
    have hz : P.eval (s i) - v i * Q.eval (s i) = 0 := by
      simpa [P, Q, u] using hh
    have he := congrArg f (sub_eq_zero.mp hz)
    simpa only [Polynomial.eval_intCast_map, Int.cast_id, map_mul, f, Int.coe_castRingHom] using he
  have hcross : (P.map f) * B = A * (Q.map f) := by
    apply q_85 A B _ _
      (Finset.univ.image (fun i => (s i : ℂ)))
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · have hsQ : Function.Injective (fun i => (s i : ℂ)) := Int.cast_injective.comp hs
      rw [Finset.card_image_of_injective _ hsQ, Finset.card_univ]
      exact hcard
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [heval', heval]
      ring
  obtain ⟨r, hP, hQ⟩ := q_82 A B _ _ hcop hBn
    (by rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]) hcross
  have hr : r ≠ 0 := by
    intro hr
    have hzero : Q.map f = 0 := by simp [hQ, hr]
    have hcoef : Q.coeff B.natDegree = M.det := by
      have hh := congrFun hc (e.symm none)
      change q_23 s v (e (e.symm none)) ⬝ᵥ c = _ at hh
      rw [e.apply_symm_apply, q_173] at hh
      simpa [Q, u, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hz := congrArg (fun p : ℂ[X] => p.coeff B.natDegree) hzero
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, hcoef] at hz
    exact hdet (Int.cast_eq_zero.mp hz)
  exact ⟨P, Q, r, hr, hP, hQ, hpdeg, hqdeg, rfl, rfl⟩
theorem q_99 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]
theorem q_109 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    q_99 (A.map fun x => (x : ℝ)) (fun _ => B) hA
theorem q_410 {ι : Type*} {a b : ℕ} (s v : ι → ℤ)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (i : Option ι)
    (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |((q_23 s v i j : ℤ) : ℝ)| ≤ H ^ (max a b + 1) := by
  classical
  have h0 : 0 ≤ H := zero_le_one.trans hH
  cases i with
  | none =>
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simpa [q_23] using one_le_pow₀ hH (n := max a b + 1)
    · simp [q_23, Pi.single_eq_of_ne hj, pow_nonneg h0]
  | some i =>
    cases j with
    | inl j =>
      simp only [q_23, Sum.elim_inl, Int.cast_pow, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hs i) _).trans
        (pow_le_pow_right₀ hH (by have := j.isLt; omega))
    | inr j =>
      simp only [q_23, Sum.elim_inr, Int.cast_neg, Int.cast_mul,
        Int.cast_pow, abs_neg, abs_mul, abs_pow]
      calc
        |(v i : ℝ)| * |(s i : ℝ)| ^ j.val ≤ H * H ^ j.val :=
          mul_le_mul (hv i) (pow_le_pow_left₀ (abs_nonneg _) (hs i) _)
            (by positivity) h0
        _ = H ^ (j.val + 1) := by rw [pow_succ]; ring
        _ ≤ H ^ (max a b + 1) := pow_le_pow_right₀ hH (by have := j.isLt; omega)
theorem q_334 {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(q_97 s v e j : ℝ)| ≤
      (Nat.factorial (a + b + 2) : ℝ) * H ^ ((max a b + 1) * (a + b + 2)) := by
  classical
  unfold q_97
  rw [Matrix.cramer_apply]
  have h := q_109
    ((q_57 s v e).updateCol j (fun j => if e j = none then 1 else 0))
    (H ^ (max a b + 1)) (fun i j' => ?_)
  · simpa only [Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      show a + 1 + (b + 1) = a + b + 2 by omega] using h
  · by_cases hj : j' = j
    · subst j'
      simp only [Matrix.updateCol_self]
      split_ifs
      · simpa using one_le_pow₀ hH (n := max a b + 1)
      · simp [pow_nonneg (zero_le_one.trans hH)]
    · rw [Matrix.updateCol_ne hj]
      exact q_410 s v H hH hs hv (e i) j'
def q_40 (D : ℕ) (H : ℝ) : ℝ :=
  (Nat.factorial (2 * D + 2) : ℝ) * H ^ ((D + 1) * (2 * D + 2))
theorem q_102 (D : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    1 ≤ q_40 D H := by
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos (2 * D + 2))
    (one_le_pow₀ hH)
theorem q_80 {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (D : ℕ) (ha : a ≤ D) (hb : b ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(q_97 s v e j : ℝ)| ≤ q_40 D H := by
  apply (q_334 s v e H hH hs hv j).trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le (show a + b + 2 ≤ 2 * D + 2 by omega)
  · exact pow_le_pow_right₀ hH (Nat.mul_le_mul (by omega) (by omega))
  · positivity
  · positivity
theorem q_278 (P Q : ℤ[X]) (H : ℝ) (hH : 0 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ H) (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ H) :
    |(P.resultant Q : ℝ)| ≤ (Nat.factorial (P.natDegree + Q.natDegree) : ℝ) *
      H ^ (P.natDegree + Q.natDegree) := by
  unfold Polynomial.resultant
  apply (q_109 _ H ?_).trans_eq
  · simp only [Fintype.card_fin]
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simpa using hH
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simpa using hH
theorem q_209 (A B : ℂ[X]) (P Q : ℤ[X])
    (hcop : IsCoprime A B) (r : ℂ) (hr : r ≠ 0)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) : P.resultant Q ≠ 0 := by
  have hcop' : IsCoprime (P.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ)) := by
    rw [hP, hQ]
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨C r⁻¹ * u, C r⁻¹ * v, ?_⟩
    calc
      C r⁻¹ * u * (C r * A) + C r⁻¹ * v * (C r * B) =
          C r⁻¹ * C r * (u * A + v * B) := by ring
      _ = 1 := by rw [huv, ← Polynomial.C_mul]; simp [hr]
  have hh := Polynomial.resultant_ne_zero _ _ hcop'
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at hh
  exact fun hz => hh (by simp only [hz, map_zero])
theorem q_263 {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ i, |(s i : ℝ)| ≤ H)
    (hvH : ∀ i, |(v i : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ q_40 D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ q_40 D H) := by
  obtain ⟨P, Q, r, hr, hP, hQ, hpdeg, _, hPc, hQc⟩ :=
    q_166 A B hcop hBn s v hs hcard heval e
  have hqdeg : Q.natDegree = B.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (p := Q) (f := Int.castRingHom ℂ) Int.cast_injective,
      hQ, Polynomial.natDegree_C_mul hr]
  refine ⟨P, Q, r, hr, hP, hQ, hpdeg.trans hA, hqdeg,
    q_209 A B P Q hcop r hr hP hQ, ?_, ?_⟩
  · intro j
    rw [hPc]
    by_cases hj : j < A.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact q_80 s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (q_102 D hH))
  · intro j
    rw [hQc]
    by_cases hj : j < B.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact q_80 s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (q_102 D hH))
theorem q_343 (A B : ℂ[X]) (P Q : ℤ[X]) (r : ℂ)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) (s v : ℤ)
    (hv : A.eval (s : ℂ) = (v : ℂ) * B.eval (s : ℂ)) :
    P.eval s = v * Q.eval s := by
  apply Int.cast_injective (α := ℂ)
  have hp := congrArg (Polynomial.eval (s : ℂ)) hP
  have hq := congrArg (Polynomial.eval (s : ℂ)) hQ
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_intCast_map, Int.coe_castRingHom, Int.cast_id] at hp hq
  push_cast
  rw [hp, hq, hv]
  ring
theorem q_154
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℤ)
    (heval : ∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ))
    (hcard : A.natDegree + B.natDegree < S.card)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ s ∈ S, |(s : ℝ)| ≤ H)
    (hvH : ∀ s ∈ S, |(v s : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ q_40 D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ q_40 D H) ∧
      ∀ s ∈ S, P.eval s = v s * Q.eval s := by
  classical
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
  let e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option T :=
    Fintype.equivOfCardEq (by simp [hTc]; omega)
  obtain ⟨P, Q, r, _, hP, hQ, hpdeg, hqdeg, hres, hpH, hqH⟩ :=
    q_263 A B hcop hBn
      (fun s : T => s.val) (fun s : T => v s.val) Subtype.val_injective
      (by simp [hTc])
      (fun s => heval s.val (hTS s.property)) e D hA hB H hH
      (fun s => hsH s.val (hTS s.property)) (fun s => hvH s.val (hTS s.property))
  refine ⟨P, Q, hpdeg, hqdeg, hres, hpH, hqH, ?_⟩
  intro s hs
  exact q_343 A B P Q r hP hQ s (v s) (heval s hs)
def q_50 (D : ℕ) : ℝ :=
  (Nat.factorial (2 * D) : ℝ) * (Nat.factorial (2 * D + 2) : ℝ) ^ (2 * D)
def q_49 (D : ℕ) : ℕ := 2 * D * ((D + 1) * (2 * D + 2))
theorem q_265 (D : ℕ) : 0 < q_50 D := by
  unfold q_50
  positivity
theorem q_264 {D : ℕ} (hD : 0 < D) :
    0 < q_49 D := by
  unfold q_49
  positivity
theorem q_153 (P Q : ℤ[X]) (D : ℕ)
    (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ q_40 D H)
    (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ q_40 D H) :
    |(P.resultant Q : ℝ)| ≤ q_50 D * H ^ q_49 D := by
  have hi := q_102 D hH
  apply (q_278 P Q (q_40 D H)
    (zero_le_one.trans hi) hP hQ).trans
  calc
    _ ≤ (Nat.factorial (2 * D) : ℝ) * q_40 D H ^ (2 * D) := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le (show P.natDegree + Q.natDegree ≤ 2 * D by omega)
      · exact pow_le_pow_right₀ hi (by omega)
      · positivity
      · positivity
    _ = q_50 D * H ^ q_49 D := by
      simp only [q_40, q_50, q_49,
        mul_pow, ← pow_mul]
      rw [Nat.mul_comm ((D + 1) * (2 * D + 2)) (2 * D)]
      ring
open Filter
theorem q_492 (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + (r - 1)⁻¹) * r ^ a := by
  have h₁ := a.cast_le_pow_div_sub hr
  have h₂ : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  calc
    (a : ℝ) + 1 ≤ r ^ a / (r - 1) + r ^ a := add_le_add h₁ h₂
    _ = (1 + (r - 1)⁻¹) * r ^ a := by ring
theorem q_452 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have hh : 0 ≤ (r - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨c ^ N, pow_pos hc0 _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < N
    · rw [if_pos hsmall]
      exact (q_492 r hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _)
        hc0.le)
    · rw [if_neg hsmall, one_mul]
      have hh : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p))
      exact hh.trans (pow_le_pow_left₀ (by norm_num) (hN p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < N then c else 1) ≤ c ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hc
    exact (Finset.card_le_card (show n.primeFactors.filter (fun p => p < N) ⊆
      Finset.range N from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)).trans
        (by rw [Finset.card_range])
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) ε,
      mul_comm ε, Real.rpow_natCast_mul (Nat.cast_nonneg _) _ ε]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then c else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ c ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconstant (by positivity)
theorem q_279 (D : ℕ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (H : ℝ), 1 ≤ H →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ H) → (∀ s ∈ S, |(v s : ℝ)| ≤ H) →
      (S.card : ℝ) ≤ C * H ^ ε := by
  let E := q_49 D
  have hE : (0 : ℝ) < E := by exact_mod_cast q_264 hD
  let δ := ε / (E : ℝ)
  have hδ : 0 < δ := div_pos hε hE
  obtain ⟨c, hc, hdiv⟩ := q_452 δ hδ
  let K := q_50 D
  have hK : 0 < K := q_265 D
  let C : ℝ := (2 * D : ℕ) + (2 * D : ℕ) * c * K ^ δ
  have h2D : (0 : ℝ) < (2 * D : ℕ) := by exact_mod_cast (by omega : 0 < 2 * D)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v H hH heval hsH hvH
  have hHε : 1 ≤ H ^ ε := Real.one_le_rpow hH hε.le
  by_cases hcard : A.natDegree + B.natDegree < S.card
  · have hBn : B ≠ 0 := by
      intro hz
      simp only [hz, Polynomial.natDegree_zero, lt_self_iff_false] at hBpos
    obtain ⟨P, Q, hPdeg, hQdeg, hres, hP, hQ, hpq⟩ :=
      q_154 A B hcop hBn S v heval hcard D hAdeg hBdeg
        H hH hsH hvH
    have hi : S.filter (fun s => Q.eval s ∣ P.eval s) = S := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      rw [hpq s hs]
      exact dvd_mul_left _ _
    have hτ := q_210 P Q (by omega) hres S
    rw [hi] at hτ
    have hR : ((P.resultant Q).natAbs : ℝ) ≤ K * H ^ E := by
      have hab : ((P.resultant Q).natAbs : ℝ) = |(P.resultant Q : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hab]
      exact q_153 P Q D hPdeg (hQdeg ▸ hBdeg) H hH hP hQ
    have hpowers : (K * H ^ E) ^ δ = K ^ δ * H ^ ε := by
      rw [Real.mul_rpow hK.le (pow_nonneg (zero_le_one.trans hH) _),
        ← Real.rpow_natCast_mul (zero_le_one.trans hH)]
      congr 1
      dsimp [δ]
      rw [mul_div_cancel₀ _ hE.ne']
    calc
      (S.card : ℝ) ≤ ((2 * Q.natDegree : ℕ) : ℝ) *
          ((P.resultant Q).natAbs.divisors.card : ℝ) := by exact_mod_cast hτ
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * (((P.resultant Q).natAbs : ℝ) ^ δ)) := by
        apply mul_le_mul
        · exact_mod_cast Nat.mul_le_mul_left 2 (hQdeg ▸ hBdeg)
        · exact hdiv _
        · positivity
        · positivity
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * ((K * H ^ E) ^ δ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hR hδ.le) hc.le) h2D.le
      _ = (((2 * D : ℕ) : ℝ) * c * K ^ δ) * H ^ ε := by rw [hpowers]; ring
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        linarith
  · have hsmall : (S.card : ℝ) ≤ (2 * D : ℕ) := by exact_mod_cast (by omega : S.card ≤ 2 * D)
    calc
      (S.card : ℝ) ≤ (2 * D : ℕ) := hsmall
      _ ≤ ((2 * D : ℕ) : ℝ) * H ^ ε := le_mul_of_one_le_right h2D.le hHε
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        have hnonneg : 0 ≤ ((2 * D : ℕ) : ℝ) * c * K ^ δ := by positivity
        linarith
theorem rational_integer_values_uniform (D : ℕ) (hD : 0 < D)
    (a b C₀ : ℝ) (ha : 0 < a) (_hb : 0 < b) (_hC₀ : 0 < C₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (X : ℝ), 2 ≤ X →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ C₀ * X ^ a) →
      (∀ s ∈ S, |(v s : ℝ)| ≤ C₀ * X ^ b) →
      (S.card : ℝ) ≤ C * X ^ ε := by
  let M := max a b
  have hM : 0 < M := lt_of_lt_of_le ha (le_max_left _ _)
  let K := max 1 C₀
  have hK : 1 ≤ K := le_max_left _ _
  let δ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  obtain ⟨c, hc, h⟩ := q_279 D hD δ hδ
  refine ⟨c * K ^ δ, by positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v X hX heval hsX hvX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXM : 1 ≤ X ^ M := Real.one_le_rpow hX1 hM.le
  have hH : 1 ≤ K * X ^ M := one_le_mul_of_one_le_of_one_le hK hXM
  have hbound (c₁ : ℝ) (hc₁ : c₁ ≤ M) : C₀ * X ^ c₁ ≤ K * X ^ M := by
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hX1 hc₁)
      (by positivity) (zero_le_one.trans hK)
  have hh := h A B hcop hBpos hAdeg hBdeg S v (K * X ^ M) hH heval
    (fun s hs => (hsX s hs).trans (hbound a (le_max_left _ _)))
    (fun s hs => (hvX s hs).trans (hbound b (le_max_right _ _)))
  have hp : (K * X ^ M) ^ δ = K ^ δ * X ^ ε := by
    rw [Real.mul_rpow (zero_le_one.trans hK) (Real.rpow_nonneg hX0 _),
      ← Real.rpow_mul hX0]
    congr 1
    dsimp [δ]
    rw [mul_div_cancel₀ _ hM.ne']
  simpa only [hp, mul_assoc] using hh
end QuarticPowerFree.ComplexValues
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical
theorem q_275 {K A : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] (x : A) (hx : IsAlgebraic K x) :
    ∃ c : K, algebraMap K A c = x := by
  have hi := hx.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have he := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd,
    (minpoly.monic hi).leadingCoeff, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact he.symm⟩
theorem q_363 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hI : q_0 I ≤ 1) (x y : Fin n)
    (hx : Transcendental K (Ideal.Quotient.mk I (X x))) :
    ∃ q : MvPolynomial (Fin 2) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree:ℚ) ≤ q_16 I ∧
      (∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) := by
  have hind : AlgebraicIndependent K
      (fun a : Fin 1 => Ideal.Quotient.mk I (X (![y,x] a.succ))) := by
    apply algebraicIndependent_unique_type_iff.mpr
    simpa using hx
  have hdim : q_0 I = 1 := by
    have htr := q_45 I (q_8 I) (q_3 I)
    have hh := hind.lift_cardinalMk_le_trdeg
    rw [← htr] at hh
    have hl : 1 ≤ q_0 I := by simpa [q_0] using hh
    omega
  obtain ⟨q,hq,hd,hb,hker⟩ := q_145 I (q_8 I)
    hI (q_3 I) ![y,x] hind
  refine ⟨q,hq,hd,?_,hker⟩
  simpa only [q_16,hdim] using hb
noncomputable def q_25 (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (finSuccEquiv K 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1)))
@[simp] theorem binaryPolynomialEquiv_natDegree {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) : (q_25 K q).natDegree = q.degreeOf 0 := by
  rw [q_25,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,
    Polynomial.natDegree_map_eq_of_injective (uniqueAlgEquiv K (Fin 1)).injective,
    natDegree_finSuccEquiv]
theorem q_347 {K A : Type*} [CommSemiring K] [CommSemiring A]
    (f : K →+* A) (x y : A) (q : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom f x) y (q_25 K q) =
      MvPolynomial.eval₂ f ![y,x] q := by
  let e : MvPolynomial (Fin 2) K →+* A :=
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f x) y).comp
      (q_25 K).toRingHom
  have he : e = MvPolynomial.eval₂Hom f ![y,x] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e,q_25,finSuccEquiv_apply,uniqueAlgEquiv]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e,q_25,finSuccEquiv_apply,uniqueAlgEquiv]
      · simp [e,q_25,finSuccEquiv_apply,uniqueAlgEquiv]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →+* A => g q) he
theorem q_258 {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 1) K) : (uniqueAlgEquiv K (Fin 1) q).natDegree ≤ q.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coeff_uniqueAlgEquiv]
  apply coeff_eq_zero_of_totalDegree_lt
  change q.totalDegree < (Finsupp.single (default : Fin 1) m).sum (fun _ e => e)
  rw [Finsupp.sum_single_index (by simp)]
  exact hm
theorem q_129 {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) (i : ℕ) :
    ((q_25 K q).coeff i).natDegree ≤ q.totalDegree := by
  simp only [q_25,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]
  by_cases hz : (finSuccEquiv K 1 q).coeff i = 0
  · simp [hz]
  · exact (q_258 _).trans
      (Nat.le_sub_of_add_le (totalDegree_coeff_finSuccEquiv_add_le q i hz) |>.trans (Nat.sub_le _ _))
theorem q_159 {K : Type*} [Field K]
    (q : MvPolynomial (Fin 2) K) (hq : Irreducible q) (hd : q.degreeOf 0 = 1) :
    ∃ A B : Polynomial K, IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree ≤ q.totalDegree ∧
      B.natDegree ≤ q.totalDegree ∧
      ∀ {S : Type*} [CommRing S] (f : K →+* S) (x y : S),
        MvPolynomial.eval₂ f ![y,x] q = 0 ↔
          A.eval₂ f x = y * B.eval₂ f x := by
  let p := q_25 K q
  have hp : Irreducible p := (MulEquiv.irreducible_iff (q_25 K)).mpr hq
  have hpd : p.natDegree = 1 := (binaryPolynomialEquiv_natDegree q).trans hd
  have he : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
    simpa only [hpd] using Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hpd))
  have hbn : p.coeff 1 ≠ 0 := by
    rw [← hpd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero
  have prim := hp.isPrimitive (by rw [hpd]; decide)
  have hcop : IsCoprime (p.coeff 0) (p.coeff 1) := by
    apply IsRelPrime.isCoprime
    intro d hd0 hd1
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp prim
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i = 0
    · subst i; exact hd0
    by_cases hi1 : i = 1
    · subst i; exact hd1
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  refine ⟨-p.coeff 0,p.coeff 1,hcop.neg_left,hbn,?_,q_129 q 1,?_⟩
  · simpa using q_129 q 0
  · intro S _ f x y
    rw [← q_347,show q_25 K q = p from rfl]
    conv_lhs => rw [he]
    simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
      Polynomial.eval₂_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_neg]
    constructor <;> intro h <;> linear_combination -h
noncomputable def q_48 {M : ℕ} (i : Fin 2 × Fin (M+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.1.val + Finsupp.single 1 i.2.val
theorem q_274 (M : ℕ) :
    Function.Injective (q_48 (M := M)) := by
  intro i j h
  have h0 := congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
  have h1 := congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
  simp only [q_48,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1:Fin 2) ≠ 0 by decide),add_zero,zero_add] at h0 h1
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)
theorem q_281 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) (M : ℕ) :
    LinearIndependent K (fun i : Fin 2 × Fin (M+1) =>
      Ideal.Quotient.mk I (rename ![y,x] (monomial (q_48 i) (1:K)))) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  let p : MvPolynomial (Fin 2) K := ∑ j ∈ s, c j • monomial (q_48 j) 1
  have hpker : Ideal.Quotient.mk I (rename ![y,x] p) = 0 := by
    change (Ideal.Quotient.mkₐ K I) (rename ![y,x] p) = 0
    simpa only [p,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hc
  have hpdeg : p.degreeOf 0 ≤ 1 := by
    apply (degreeOf_sum_le 0 s _).trans
    apply Finset.sup_le
    intro j _
    rw [smul_monomial,smul_eq_mul,mul_one]
    by_cases hz : c j = 0
    · simp [hz]
    · rw [degreeOf_monomial_eq _ _ hz]
      simp only [q_48,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),add_zero]
      omega
  have hp : p = 0 := by
    by_contra hp
    obtain ⟨t,ht⟩ := (hker p).mp hpker
    have hmul : q*t ≠ 0 := ht ▸ hp
    have hd := degreeOf_mul_eq (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul) (n := 0)
    rw [← ht] at hd
    omega
  have hl := (basisMonomials (Fin 2) K).linearIndependent.comp
    (q_48 (M := M)) (q_274 M)
  simp only [coe_basisMonomials,Function.comp_def] at hl
  exact linearIndependent_iff'.mp hl s c hp i hi
theorem q_273 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (a b : ℕ) (T : ℝ) (hb : ω y*a+ω x*b ≤ T) :
    Ideal.Quotient.mk I ((X y)^a*(X x)^b) ∈ q_60 I ω T := by
  classical
  have hweight : q_37 ω (Finsupp.single y a + Finsupp.single x b) = ω y*a+ω x*b := by
    simp only [q_37,Finsupp.coe_add,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial,X_pow_eq_monomial,monomial_mul,one_mul]
  apply Submodule.subset_span
  refine ⟨_,(q_69 ω hω T _).mpr (hweight ▸ hb),rfl⟩
theorem q_370 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (hx : ω x = 1)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p)
    (M : ℕ) (T : ℝ) (hT : (M:ℝ)+ω y ≤ T) :
    2*(M+1) ≤ q_32 I ω T := by
  classical
  let v := fun i : Fin 2 × Fin (M+1) =>
    Ideal.Quotient.mk I (rename ![y,x] (monomial (q_48 i) (1:K)))
  have hv (i : Fin 2 × Fin (M+1)) : v i ∈ q_60 I ω T := by
    have he : rename ![y,x] (monomial (q_48 i) (1:K)) = (X y)^i.1.val*(X x)^i.2.val := by
      rw [q_48,← one_mul (1:K),← monomial_mul,← X_pow_eq_monomial,← X_pow_eq_monomial]
      simp
    dsimp only [v]
    rw [he]
    apply q_273 I ω hω x y _ _ T
    rw [hx,one_mul]
    have h1 : (i.1.val:ℝ) ≤ 1 := by exact_mod_cast (show i.1.val ≤ 1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    have hh := mul_le_mul_of_nonneg_left h1 (hω y).le
    linarith
  let u : (Fin 2 × Fin (M+1)) → q_60 I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (q_60 I ω T).subtype
    (q_281 I x y q hq hker M)
  simpa only [Fintype.card_prod,Fintype.card_fin,q_32] using hu.fintype_card_le_finrank
theorem q_127 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (hx : ω x = 1)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) :
    ∀ T : ℝ, 0 ≤ T → 2*T-2*(ω y+1) ≤ q_32 I ω T := by
  intro T _
  by_cases hT : ω y ≤ T
  · have hf : (⌊T-ω y⌋₊:ℝ)+ω y ≤ T := by linarith [Nat.floor_le (sub_nonneg.mpr hT)]
    have hb := q_370 I ω hω x y hx q hq hker ⌊T-ω y⌋₊ T hf
    have hbr : 2*((⌊T-ω y⌋₊:ℝ)+1) ≤ q_32 I ω T := by exact_mod_cast hb
    have hl := Nat.lt_floor_add_one (T-ω y)
    linarith
  · have hh : (0:ℝ) ≤ q_32 I ω T := Nat.cast_nonneg _
    linarith
theorem q_95 {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) (x y : R) (A B : Polynomial K) (hB : B ≠ 0)
    (hdeg : B.natDegree = 0) (he : A.eval₂ φ x = y*B.eval₂ φ x) :
    ∃ P : Polynomial K, P.eval₂ φ x = y := by
  have hBc : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hb : B.coeff 0 ≠ 0 := by intro h; apply hB; rw [hBc,h,Polynomial.C_0]
  refine ⟨Polynomial.C (B.coeff 0)⁻¹ * A,?_⟩
  have hev : B.eval₂ φ x = φ (B.coeff 0) := by
    conv_lhs => rw [hBc]
    rw [Polynomial.eval₂_C]
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,he,hev,← mul_assoc,mul_comm (φ _),mul_assoc,
    ← map_mul,inv_mul_cancel₀ hb,map_one,mul_one]
theorem q_132 {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (f Y Z : Polynomial K) (k : ℕ) (hk : 2 ≤ k)
    (hf : Squarefree f) (x y z : R) (hx : Transcendental K x)
    (hY : Polynomial.aeval x Y = y) (hZ : Polynomial.aeval x Z = z)
    (he : Polynomial.aeval x f = y*z^k) :
    ∃ c : K, algebraMap K R c = z := by
  have hid : f = Y*Z^k := (transcendental_iff_injective.mp hx) (by simpa only [map_mul,map_pow,hY,hZ] using he)
  have hu : IsUnit Z := by
    by_contra hn
    have hs : Squarefree (Z^k) := hf.squarefree_of_dvd ⟨Y,by rw [hid]; ring⟩
    have hh := hs.eq_zero_or_one_of_pow_of_not_isUnit hn
    omega
  have hz := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)
  refine ⟨Z.coeff 0,?_⟩
  rw [← hZ]
  conv_rhs => rw [hz]
  rw [Polynomial.aeval_C]
theorem q_133 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K)
    (hq : Ideal.Quotient.mk I (rename ![y,x] q) = 0) :
    MvPolynomial.eval₂ (algebraMap K (MvPolynomial (Fin n) K ⧸ I))
      ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] q = 0 := by
  have he : MvPolynomial.aeval ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] =
      (Ideal.Quotient.mkₐ K I).comp (rename ![y,x]) := by
    ext i
    fin_cases i <;> simp
  change (MvPolynomial.aeval _) q = 0
  rw [he]
  exact hq
theorem q_387 (I : Ideal (MvPolynomial (Fin 3) ℂ)) [I.IsPrime]
    (hI : q_0 I ≤ 1) (e : ℕ) (hdeg : q_16 I ≤ e)
    (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (f : Polynomial ℂ) (hf : Squarefree f) (k : ℕ) (hk : 2 ≤ k)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X 0)) f =
      Ideal.Quotient.mk I (X 1) * (Ideal.Quotient.mk I (X 2))^k) :
    (∃ c : ℂ, algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I) c = Ideal.Quotient.mk I (X 0)) ∨
    (∃ (j : Fin 3) (A B : Polynomial ℂ), (j = 1 ∨ j = 2) ∧ IsCoprime A B ∧
      0 < B.natDegree ∧ A.natDegree ≤ e ∧ B.natDegree ≤ e ∧
      Polynomial.aeval (Ideal.Quotient.mk I (X 0)) A =
        Ideal.Quotient.mk I (X j) * Polynomial.aeval (Ideal.Quotient.mk I (X 0)) B) ∨
    (∃ c : ℂ, algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I) c = Ideal.Quotient.mk I (X 2)) ∨
    (∀ T : ℝ, 1 ≤ T → 2*T-2*(ω 1+ω 2+1) ≤ q_32 I ω T) := by
  by_cases hx : IsAlgebraic ℂ (Ideal.Quotient.mk I (X 0))
  · exact Or.inl (q_275 _ hx)
  have relations (j : Fin 3) := q_363 I hI 0 j hx
  obtain ⟨qY,hqY,hdY,hbY,hkerY⟩ := relations 1
  obtain ⟨qZ,hqZ,hdZ,hbZ,hkerZ⟩ := relations 2
  have hbY' : qY.totalDegree ≤ e := by exact_mod_cast hbY.trans hdeg
  have hbZ' : qZ.totalDegree ≤ e := by exact_mod_cast hbZ.trans hdeg
  by_cases h2Y : 2 ≤ qY.degreeOf 0
  · right; right; right
    intro T hT
    have hh := q_127 I ω hω 0 1 hω0 qY h2Y hkerY T (by linarith)
    linarith [hω 2]
  by_cases h2Z : 2 ≤ qZ.degreeOf 0
  · right; right; right
    intro T hT
    have hh := q_127 I ω hω 0 2 hω0 qZ h2Z hkerZ T (by linarith)
    linarith [hω 1]
  obtain ⟨AY,BY,hcopY,hBY,hAYb,hBYb,hY⟩ := q_159 qY hqY (by omega)
  obtain ⟨AZ,BZ,hcopZ,hBZ,hAZb,hBZb,hZ⟩ := q_159 qZ hqZ (by omega)
  have heY := (hY (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    (Ideal.Quotient.mk I (X 0)) (Ideal.Quotient.mk I (X 1))).mp
    (q_133 I 0 1 qY ((hkerY qY).mpr (dvd_refl _)))
  have heZ := (hZ (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    (Ideal.Quotient.mk I (X 0)) (Ideal.Quotient.mk I (X 2))).mp
    (q_133 I 0 2 qZ ((hkerZ qZ).mpr (dvd_refl _)))
  by_cases hYpos : 0 < BY.natDegree
  · exact Or.inr (Or.inl ⟨1,AY,BY,Or.inl rfl,hcopY,hYpos,hAYb.trans hbY',hBYb.trans hbY',heY⟩)
  by_cases hZpos : 0 < BZ.natDegree
  · exact Or.inr (Or.inl ⟨2,AZ,BZ,Or.inr rfl,hcopZ,hZpos,hAZb.trans hbZ',hBZb.trans hbZ',heZ⟩)
  obtain ⟨Y,hY⟩ := q_95 (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    _ _ AY BY hBY (by omega) heY
  obtain ⟨Z,hZ⟩ := q_95 (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    _ _ AZ BZ hBZ (by omega) heZ
  exact Or.inr (Or.inr (Or.inl (q_132 f Y Z k hk hf _ _ _ hx hY hZ he)))
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
section
open Polynomial
open scoped BigOperators Classical
theorem q_322 (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : Polynomial.C (p:ℤ) ∣ f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hh := congrArg (fun g : Polynomial (ZMod p) => g.coeff i) hz
    simpa using hh
  have hu := Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hf (p:ℤ) hd
  have he := Int.isUnit_iff_natAbs_eq.mp hu
  exact hp.ne_one (by simpa using he)
theorem q_262 (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) (X : ℝ) (hXp : X < p) (S : Finset (Fin 3 → ℤ))
    (hinj : Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set (Fin 3 → ℤ)))
    (hrange : ∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X)
    (hroot : ∀ z ∈ S, (p:ℤ) ∣ f.eval (z 0)) : S.card ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := q_322 f hf p hp
  have hmap : Set.MapsTo (fun z : Fin 3 → ℤ => (z 0 : ZMod p)) (S:Set _) (F.roots.toFinset:Set _) := by
    intro z hz
    rw [Finset.mem_coe,Multiset.mem_toFinset,Polynomial.mem_roots hF]
    change F.eval (z 0 : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,Polynomial.eval_map]
    change f.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) (z 0)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hroot z hz)
  have hmodinj : Set.InjOn (fun z : Fin 3 → ℤ => (z 0 : ZMod p)) (S:Set _) := by
    intro u hu v hv huv
    apply hinj hu hv
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (u 0) (v 0) p).mp huv
    obtain ⟨hu1,hu2⟩ := hrange u hu
    obtain ⟨hv1,hv2⟩ := hrange v hv
    have hh : |((v 0-u 0:ℤ):ℝ)| < (p:ℝ) := by
      push_cast
      rw [abs_lt]
      constructor <;> linarith
    have hh' : (v 0-u 0).natAbs < p := by
      exact_mod_cast (show ((v 0-u 0).natAbs:ℝ) < p by simpa only [Nat.cast_natAbs,Int.cast_abs] using hh)
    have he : v 0-u 0 = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hh')
    exact (sub_eq_zero.mp he).symm
  calc
    S.card ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hmodinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le
end
open MvPolynomial
open scoped BigOperators Classical
noncomputable def q_325 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : q_64 I z) :
    (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (fun j => (z j : K))) (by
    intro p hp
    exact hz p hp)
@[simp] theorem pointEvaluation_X {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : q_64 I z) (j : Fin n) :
    q_325 I z hz (Ideal.Quotient.mk I (X j)) = (z j:K) := by
  change MvPolynomial.aeval (fun i => (z i:K)) (X j) = _
  simp
theorem q_67 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : q_64 I z) (j : Fin n)
    (c : K) (hc : algebraMap K (MvPolynomial (Fin n) K ⧸ I) c = Ideal.Quotient.mk I (X j)) :
    (z j:K) = c := by
  have he := congrArg (q_325 I z hz) hc
  simpa only [AlgHom.commutes,Algebra.algebraMap_self, RingHom.id_apply,pointEvaluation_X] using he.symm
theorem q_280 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : q_64 I z) (x j : Fin n)
    (A B : Polynomial K)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X x)) A =
      Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X x)) B) :
    A.eval (z x:K) = (z j:K)*B.eval (z x:K) := by
  have hh := congrArg (q_325 I z hz) he
  rw [map_mul,← Polynomial.aeval_algHom_apply,← Polynomial.aeval_algHom_apply] at hh
  simpa only [pointEvaluation_X,Polynomial.aeval_def,
    Algebra.algebraMap_self,Polynomial.eval₂_id] using hh
theorem q_403 (D : ℕ) (hD : 0 < D) (ω : Fin 3 → ℝ)
    (hω : ∀ i, 0 < ω i) (hω0 : ω 0 = 1) (Cbox : ℝ) (hCbox : 0 < Cbox)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin 3 → ℤ)),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ i, |(z i:ℝ)| ≤ Cbox*X^(ω i)) →
      ∀ (j : Fin 3) (A B : Polynomial ℂ), (j = 1 ∨ j = 2) → IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      (∀ z ∈ S, A.eval (z 0:ℂ) = (z j:ℂ)*B.eval (z 0:ℂ)) →
      (S.card:ℝ) ≤ C*X^ε := by
  classical
  obtain ⟨C,hC,hbound⟩ := ComplexValues.rational_integer_values_uniform D hD 1 (max (ω 1) (ω 2)) Cbox
    (by norm_num) (lt_of_lt_of_le (hω 1) (le_max_left _ _)) hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S hinj hbox j A B hj hcop hB hAD hBD he
  let v : ℤ → ℤ := fun s => if hs : ∃ z ∈ S, z 0 = s then hs.choose j else 0
  have hv (z) (hz : z ∈ S) : v (z 0) = z j := by
    have hs : ∃ u ∈ S, u 0 = z 0 := ⟨z,hz,rfl⟩
    dsimp only [v]
    rw [dif_pos hs]
    have hu := hinj hs.choose_spec.1 hz hs.choose_spec.2
    exact congrArg (fun u => u j) hu
  have hcard : (S.image fun z => z 0).card = S.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply hbound A B hcop hB hAD hBD _ v X hX
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    rw [hv z hz]
    exact he z hz
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    simpa only [hω0] using hbox z hz 0
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    rw [hv z hz]
    apply (hbox z hz j).trans
    gcongr
    · linarith
    · rcases hj with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
theorem q_271 (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hsq : Squarefree (f.map (Int.castRingHom ℂ))) (k : ℕ) (hk : 2 ≤ k)
    (e : ℕ) (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (Cbox : ℝ) (hCbox : 0 < Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin 3 → ℤ)),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0)) →
      ∀ (I : Ideal (MvPolynomial (Fin 3) ℂ)), I.IsPrime →
      q_0 I ≤ 1 → q_16 I ≤ e →
      (∀ z ∈ S, q_64 I z) →
      (Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X 0)) (f.map (Int.castRingHom ℂ)) =
        Ideal.Quotient.mk I (MvPolynomial.X 1)*(Ideal.Quotient.mk I (MvPolynomial.X 2))^k) →
      (S.card:ℝ) ≤ C*X^ε ∨
        (∀ T : ℝ, 1 ≤ T → 2*T-2*(ω 1+ω 2+1) ≤ q_32 I ω T) := by
  classical
  obtain ⟨Cr,hCr,hcount⟩ := q_403 (e+1) (by omega) ω hω hω0 Cbox hCbox ε hε
  let C : ℝ := 1+Cr+f.natDegree
  have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) f.natDegree]
  refine ⟨C,hC,?_⟩
  intro X hX S hinj hbox hrange hselected I hI hdim hdeg hon he
  let : I.IsPrime := hI
  have hpow : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
  have hsmall (a : ℕ) (ha : S.card ≤ a) (haC : (a:ℝ) ≤ C) : (S.card:ℝ) ≤ C*X^ε := by
    have ha' : (S.card:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    exact ha'.trans (haC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hpow))
  rcases q_387 I hdim e hdeg ω hω hω0 (f.map (Int.castRingHom ℂ)) hsq k hk he with
    ⟨c,hc⟩ | ⟨j,A,B,hj,hcop,hB,hAD,hBD,hrel⟩ | ⟨c,hc⟩ | hH
  · left
    apply hsmall 1 _ (by simpa using hC)
    apply Finset.card_le_one.mpr
    intro u hu v hv
    apply hinj hu hv
    apply Int.cast_injective (α := ℂ)
    exact (q_67 I u (hon u hu) 0 c hc).trans
      (q_67 I v (hon v hv) 0 c hc).symm
  · left
    have hC' : Cr ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) f.natDegree]
    exact (hcount X hX S hinj hbox j A B hj hcop hB (by omega) (by omega)
      (fun z hz => q_280 I z (hon z hz) 0 j A B hrel)).trans
      (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (by linarith) _))
  · left
    by_cases hn : S.Nonempty
    · obtain ⟨u,hu⟩ := hn
      obtain ⟨p,hp,hup,hXp,_⟩ := hselected u hu
      have hroot (z) (hz : z ∈ S) : (p:ℤ) ∣ f.eval (z 0) := by
        obtain ⟨q,hq,hzq,_,hroot⟩ := hselected z hz
        have heq : z 2 = u 2 := Int.cast_injective ((q_67 I z (hon z hz) 2 c hc).trans
          (q_67 I u (hon u hu) 2 c hc).symm)
        rw [hup,hzq] at heq
        have hqp : q = p := by exact_mod_cast heq
        simpa only [hqp] using hroot
      apply hsmall f.natDegree (q_262 f hf p hp X hXp S hinj hrange hroot)
      dsimp [C]
      linarith
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · exact Or.inr hH
noncomputable def q_46 {K : Type*} [CommRing K] (f : Polynomial K) (k : ℕ) :
    MvPolynomial (Fin 3) K := Polynomial.eval₂ C (X 0) f - X 1*(X 2)^k
noncomputable def q_42 (K : Type*) [CommRing K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (renameEquiv K (Equiv.swap 0 1)).trans (finSuccEquiv K 2)
@[simp] theorem directSurfaceEquiv_X0 {K : Type*} [CommRing K] :
    q_42 K (X 0) = Polynomial.C (X 0) := by
  simp [q_42,finSuccEquiv_apply]
  rfl
@[simp] theorem directSurfaceEquiv_X1 {K : Type*} [CommRing K] :
    q_42 K (X 1) = Polynomial.X := by
  simp [q_42,finSuccEquiv_apply]
@[simp] theorem directSurfaceEquiv_X2 {K : Type*} [CommRing K] :
    q_42 K (X 2) = Polynomial.C (X 1) := by
  simp [q_42,Equiv.swap_apply_of_ne_of_ne,finSuccEquiv_apply]
  rfl
@[simp] theorem directSurfaceEquiv_C {K : Type*} [CommRing K] (c : K) :
    q_42 K (C c) = Polynomial.C (C c) := by
  simp [q_42,finSuccEquiv_apply]
theorem q_388 {K : Type*} [CommRing K] (f : Polynomial K) (k : ℕ) :
    q_42 K (q_46 f k) =
      Polynomial.C (-(X 1)^k) * Polynomial.X + Polynomial.C (Polynomial.eval₂ C (X 0) f) := by
  have he : q_42 K (Polynomial.eval₂ C (X 0) f) =
      Polynomial.C (Polynomial.eval₂ C (X 0) f) := by
    induction f using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,hp,hq]
    | monomial n a => simp [Polynomial.eval₂_monomial,mul_comm]
  simp only [q_46,map_sub,he,map_mul,map_pow,directSurfaceEquiv_X1,directSurfaceEquiv_X2,
    Polynomial.C_neg]
  ring
theorem q_293 {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) :
    IsRelPrime (-(X (1:Fin 2))^k) (Polynomial.eval₂ C (X 0) f) := by
  have hn : ¬ (X (1:Fin 2) : MvPolynomial (Fin 2) K) ∣ Polynomial.eval₂ C (X 0) f := by
    intro hd
    let ψ : MvPolynomial (Fin 2) K →+* Polynomial K := eval₂Hom Polynomial.C ![Polynomial.X,0]
    have he : ψ (Polynomial.eval₂ C (X 0) f) = f := by
      clear hf hd
      induction f using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,hp,hq]
      | monomial n a => simp [Polynomial.eval₂_monomial,ψ,Polynomial.C_mul_X_pow_eq_monomial]
    have hh := map_dvd ψ hd
    apply hf
    simpa only [ψ,eval₂Hom_X',Matrix.cons_val_one,Matrix.cons_val_zero,zero_dvd_iff,he] using hh
  have hp := (MvPolynomial.X_prime (i := (1:Fin 2)) (R := K)).irreducible
  exact ((hp.isRelPrime_iff_not_dvd.mpr hn).pow_left).neg_left
theorem q_175 {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) : Irreducible (q_46 f k) := by
  apply (MulEquiv.irreducible_iff (q_42 K)).mp
  rw [q_388]
  exact Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr (pow_ne_zero _ (X_ne_zero _)))
    (q_293 f hf k)
theorem coeff_single_eval₂_C_X {σ K : Type*} [CommSemiring K] (i : σ)
    (f : Polynomial K) (n : ℕ) :
    (Polynomial.eval₂ C (X i) f).coeff (Finsupp.single i n) = f.coeff n := by
  classical
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add,MvPolynomial.coeff_add,
      Polynomial.coeff_add,hp,hq]
  | monomial m a =>
    simp [Polynomial.eval₂_monomial,C_mul_X_pow_eq_monomial,coeff_monomial,
      Polynomial.coeff_monomial,(Finsupp.single_injective i).eq_iff]
theorem q_344 {K : Type*} [CommRing K]
    (f : Polynomial K) (k n : ℕ) :
    (q_46 f k).coeff (Finsupp.single 0 n) = f.coeff n := by
  classical
  have hne : Finsupp.single (1:Fin 3) 1 + Finsupp.single 2 k ≠ Finsupp.single 0 n := by
    intro h
    have hh := congrArg (fun v : Fin 3 →₀ ℕ => v 1) h
    simp at hh
  rw [q_46,coeff_sub,coeff_single_eval₂_C_X,X_pow_eq_monomial]
  rw [X,monomial_mul,one_mul,coeff_monomial,if_neg hne,sub_zero]
theorem q_193 {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) (w : Fin 3 → ℕ) :
    f.natDegree*w 0 ≤ weightedTotalDegree w (q_46 f k) := by
  have hm : Finsupp.single 0 f.natDegree ∈ (q_46 f k).support := by
    rw [mem_support_iff,q_344]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf
  have hh := Finset.le_sup (f := Finsupp.weight w) hm
  simpa only [weightedTotalDegree,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id] using hh
theorem q_235 {σ K : Type*} [Field K]
    (F : MvPolynomial σ K) (hF : Irreducible F) : 0 < F.totalDegree := by
  by_contra hn
  have hd : F.totalDegree = 0 := by omega
  have he : F = C (F.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : F.coeff 0 ≠ 0 := by intro hh; rw [he,hh,map_zero] at hF; exact hF.ne_zero rfl
  exact hF.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical
theorem q_121 {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) :
    q_8 (Ideal.span {F}) = q_24 n F.totalDegree := by
  apply q_56
  filter_upwards [q_3 (Ideal.span {F}),
    Filter.eventually_ge_atTop F.totalDegree] with T he hT
  exact he.symm.trans (q_111 F hF T hT)
theorem q_137 {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) (hdeg : 0 < F.totalDegree) :
    q_0 (Ideal.span {F}) = n := by
  rw [q_0,q_121 F hF]
  apply le_antisymm (q_90 n F.totalDegree)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [q_63]
  exact div_ne_zero (by exact_mod_cast hdeg.ne') (by exact_mod_cast Nat.factorial_ne_zero n)
theorem q_368 {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) (hdeg : 0 < F.totalDegree) :
    q_16 (Ideal.span {F}) = F.totalDegree := by
  rw [q_16,q_137 F hF hdeg,
    q_121 F hF,q_63]
  field_simp
theorem q_392 {n h : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hIJ : I < J) (hd : q_0 I = h+1) :
    q_0 J ≤ h := by
  obtain ⟨p,hpJ,hpI⟩ := SetLike.exists_of_lt hIJ
  have hcut : I ⊔ Ideal.span {p} ≤ J := sup_le hIJ.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpJ))
  have hdeg := (q_84 I p hpI (q_8 I)
    (q_8 (I ⊔ Ideal.span {p}))
    ((q_3 I).mono (fun _ ht => ht.symm))
    ((q_3 _).mono (fun _ ht => ht.symm)) h hd.le).1
  have hnon : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ (q_8 J).eval (T:ℚ) := by
    filter_upwards [q_3 J] with T he
    rw [← he]; positivity
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      (q_8 J).eval (T:ℚ) ≤ (q_8 (I ⊔ Ideal.span {p})).eval (T:ℚ) := by
    filter_upwards [q_3 J,q_3 (I ⊔ Ideal.span {p})]
      with T hJ hI
    rw [← hJ,← hI]
    exact_mod_cast q_310 _ J hcut T
  exact (q_6 _ _ hnon hle).trans hdeg
theorem q_404 {n h : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hIJ : I ≤ J) (hdI : q_0 I = h+1) (hdJ : q_0 J = h+1) :
    I = J := by
  by_contra hne
  have h := q_392 I J (lt_of_le_of_ne hIJ hne) hdI
  omega
theorem q_147 {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (w : Fin n → ℕ) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, (w i : ℝ) = L*ω i) (T : ℝ) (hT : 0 ≤ T) :
    (q_62 w ⌊L*T⌋₊).map (Ideal.Quotient.mkₐ K I).toLinearMap ≤
      q_60 I ω T := by
  classical
  rintro y ⟨p,hp,rfl⟩
  have hs : ∀ a ∈ p.support, q_37 ω a ≤ T := by
    intro a ha
    have hh : Finsupp.weight w a ≤ ⌊L*T⌋₊ :=
      hp ha
    have he : (Finsupp.weight w a : ℝ) = L*q_37 ω a := by
      rw [Finsupp.weight_eq_sum]
      simp only [Nat.cast_sum,q_37,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsmul_eq_mul,Nat.cast_mul,hw]
      norm_cast
      ring
    have hhN : (Finsupp.weight w a : ℝ) ≤ (⌊L*T⌋₊:ℕ) := by exact_mod_cast hh
    have hh' : (Finsupp.weight w a : ℝ) ≤ L*T :=
      hhN.trans (Nat.floor_le (mul_nonneg hL.le hT))
    rw [he] at hh'
    exact (mul_le_mul_iff_right₀ hL).mp hh'
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  have hm : Ideal.Quotient.mk I (monomial a (1:K)) ∈ q_60 I ω T :=
    Submodule.subset_span ⟨a,(q_69 ω hω T a).mpr (hs a ha),rfl⟩
  have he : monomial a (p.coeff a) = (p.coeff a) • monomial a (1:K) := by
    rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he]
  simpa using (q_60 I ω T).smul_mem (p.coeff a) hm
theorem q_321 {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (ω : Fin 3 → ℝ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, (q_15 a b c i : ℝ) = (a:ℝ)*ω i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ((weightedTotalDegree (q_15 a b c) F : ℕ):ℝ)*(a:ℝ)^2 /
        (2*(a*b*c:ℕ)) * T^2 - C*T ≤ q_32 (Ideal.span {F}) ω T := by
  classical
  obtain ⟨C,hC,hH⟩ := q_438 ha hb hc F hF
  let D := weightedTotalDegree (q_15 a b c) F
  let A : ℝ := D/(2*(a*b*c:ℕ))
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have habc : (0:ℝ) < (a*b*c:ℕ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let E : ℝ := A*(2*a + (D:ℝ)^2) + C*(a+1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E,hE,?_⟩
  intro T hT
  let N := ⌊(a:ℝ)*T⌋₊
  have hN : (N:ℝ) ≤ a*T := Nat.floor_le (by positivity)
  have hN' : a*T < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hrank := Submodule.finrank_mono (q_147
    (Ideal.span {F}) (q_15 a b c) ω hω (a:ℝ) ha' hw T (by linarith))
  have htarget : ((weightedTotalDegree (q_15 a b c) F : ℕ):ℝ)*(a:ℝ)^2 /
      (2*(a*b*c:ℕ))*T^2 = A*((a:ℝ)*T)^2 := by dsimp [A,D]; ring
  rw [htarget]
  by_cases hDN : D ≤ N
  · have hh := (abs_le.mp (hH N hDN)).1
    have hr : (Module.finrank K ((q_62 (q_15 a b c) N).map
        (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap):ℝ) ≤
        q_32 (Ideal.span {F}) ω T := by exact_mod_cast hrank
    have hsq : ((a:ℝ)*T)^2 ≤ (N:ℝ)^2+2*a*T := by
      have hnn : (0:ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith
    have hh' : A*(N:ℝ)^2-C*((N:ℝ)+1) ≤ q_32 (Ideal.span {F}) ω T := by
      have hv : A*(N:ℝ)^2 =
          ((weightedTotalDegree (q_15 a b c) F : ℕ):ℝ)*(N:ℝ)^2/(2*(a*b*c:ℕ)) := by
        dsimp [A,D]; ring
      rw [← hv] at hh
      linarith only [hh,hr]
    have hCs : C*((N:ℝ)+1) ≤ C*(a+1)*T := by nlinarith
    have hAs := mul_le_mul_of_nonneg_left hsq hA
    have hDterm : 0 ≤ A*(D:ℝ)^2*T := by positivity
    dsimp [E]
    nlinarith only [hAs,hh',hCs,hDterm]
  · have hND : N+1 ≤ D := by omega
    have hbound : (a:ℝ)*T ≤ D := by
      have hND' : (N:ℝ)+1 ≤ D := by exact_mod_cast hND
      linarith
    have hsq : ((a:ℝ)*T)^2 ≤ (D:ℝ)^2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hbound
    have hAs := mul_le_mul_of_nonneg_left hsq hA
    have hDterm : A*(D:ℝ)^2 ≤ A*(D:ℝ)^2*T := le_mul_of_one_le_right (by positivity) hT
    have hr : (0:ℝ) ≤ q_32 (Ideal.span {F}) ω T := Nat.cast_nonneg _
    have hother : 0 ≤ (A*(2*a)+C*(a+1))*T := by positivity
    dsimp [E]
    nlinarith
theorem q_428 {K : Type*} [Field K] (f : Polynomial K) (k : ℕ)
    (J : Ideal (MvPolynomial (Fin 3) K)) (hJ : Ideal.span {q_46 f k} ≤ J) :
    Polynomial.aeval (Ideal.Quotient.mk J (X 0)) f =
      Ideal.Quotient.mk J (X 1)*(Ideal.Quotient.mk J (X 2))^k := by
  have hz : Ideal.Quotient.mk J (q_46 f k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJ (Ideal.subset_span (Set.mem_singleton _)))
  have he : Ideal.Quotient.mk J (Polynomial.eval₂ C (X 0) f) =
      Polynomial.aeval (Ideal.Quotient.mk J (X 0)) f := by
    change (Ideal.Quotient.mkₐ K J) (Polynomial.aeval (X 0) f) = _
    exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K J) (X 0) f).symm
  simpa only [q_46,map_sub,map_mul,map_pow,he,sub_eq_zero] using hz
theorem q_228 {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Fin 3 → ℝ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, (q_15 a b c i : ℝ) = (a:ℝ)*ω i)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : (b:ℝ)*(c:ℝ) ≤ (f.natDegree:ℝ)*(a:ℝ)^2*δ^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      T^2/(2*δ^2)-C*T ≤ q_32 (Ideal.span {q_46 f k}) ω T := by
  have hF := (q_175 f hf k).ne_zero
  obtain ⟨C,hC,hH⟩ := q_321 ha hb hc (q_46 f k) hF ω hω hw
  refine ⟨C,hC,?_⟩
  intro T hT
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  let D := weightedTotalDegree (q_15 a b c) (q_46 f k)
  have hD : (f.natDegree:ℝ)*(a:ℝ) ≤ (D:ℝ) := by
    have hh := q_193 f hf k (q_15 a b c)
    simpa only [q_15,Matrix.cons_val_zero,Nat.cast_mul] using (show
      ((f.natDegree*q_15 a b c 0:ℕ):ℝ) ≤ D from by exact_mod_cast hh)
  have he : (D:ℝ)*(a:ℝ)^2/(2*(a*b*c:ℕ)) = (D:ℝ)*a/(2*(b:ℝ)*c) := by
    push_cast
    field_simp
  have hcoeff : 1/(2*δ^2) ≤ (D:ℝ)*(a:ℝ)^2/(2*(a*b*c:ℕ)) := by
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hD (show 0 ≤ (a:ℝ)*δ^2 by positivity)
    nlinarith only [hmargin,hm]
  have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)
  have hH' := hH T hT
  dsimp only [D] at hh
  have heq : 1/(2*δ^2)*T^2 = T^2/(2*δ^2) := by ring
  rw [heq] at hh
  linarith only [hh,hH']
theorem q_128 (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hsq : Squarefree (f.map (Int.castRingHom ℂ))) (k : ℕ) (hk : 2 ≤ k)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (hw : ∀ i, (q_15 a b c i : ℝ) = (a:ℝ)*ω i)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hmargin : (b:ℝ)*(c:ℝ) ≤ (f.natDegree:ℝ)*(a:ℝ)^2*δ^2)
    (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin 3 → ℤ),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0)) →
      (∀ z ∈ S, (f.map (Int.castRingHom ℂ)).eval (z 0:ℂ) = (z 1:ℂ)*(z 2:ℂ)^k) →
      (S.card:ℝ) ≤ C*X^(δ+1/2+ε) := by
  classical
  let fc := f.map (Int.castRingHom ℂ)
  have hfc : fc ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr hf.ne_zero
  have hdegfc : fc.natDegree = f.natDegree := Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) f
  let F := q_46 fc k
  have hFir : Irreducible F := q_175 fc hfc k
  have hFdeg : 0 < F.totalDegree := q_235 F hFir
  let I := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hFir.ne_zero).mpr hFir.prime
  let : I.IsPrime := hI
  have hdI : q_0 I = 2 := q_137 F hFir.ne_zero hFdeg
  have heI : q_16 I = F.totalDegree := q_368 F hFir.ne_zero hFdeg
  have hmarginc : (b:ℝ)*(c:ℝ) ≤ (fc.natDegree:ℝ)*(a:ℝ)^2*δ^2 := by rwa [hdegfc]
  obtain ⟨Cs,hCs,hHs⟩ := q_228 fc hfc k ha hb hc ω hω hw δ hδ hmarginc
  choose Kex hKex hcurve using fun e => q_271 f hf hsq k hk e ω hω hω0
    Cbox (by linarith) (ε/4) (by linarith)
  let cc := fun _ : ℕ => Cs+2*(ω 1+ω 2+1)
  have hcc : ∀ e, 0 ≤ cc e := by intro e; dsimp [cc]; linarith [hω 1,hω 2]
  let av : Fin 2 → ℝ := ![δ,1/2-δ]
  let dv : Fin 2 → ℝ := ![δ,1/2]
  have hav : ∀ i, 0 ≤ av i := by intro i; fin_cases i <;> simp [av] <;> linarith
  have hdv : ∀ i, 0 < dv i := by intro i; fin_cases i <;> simp [dv,hδ]
  have hprefix : ∀ i, dv i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => j.val ≤ i.val), av j := by
    intro i
    fin_cases i <;> norm_num [av,dv,Fin.sum_univ_two,Finset.sum_filter]
  let w := 1+∑ j, ω j
  have hsum : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => (hω j).le)
  have hwpos : 0 ≤ w := by dsimp [w]; linarith
  obtain ⟨C,Xcut,hC,hcount⟩ := q_443 3 2 0 F.totalDegree (by norm_num)
    ω hω Cbox w hCbox hwpos av dv hav hdv hprefix ε hε cc Kex hcc hKex
  refine ⟨C,max (max 2 Cbox) Xcut,hC,?_⟩
  intro X hX S hinj hbox hrange hselected heq
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hCX : Cbox ≤ X := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX)
  have hXcut : Xcut < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hmax (j : Fin 3) : ω j ≤ ∑ l, ω l :=
    Finset.single_le_sum (fun l _ => (hω l).le) (Finset.mem_univ j)
  have hbound (z) (hz : z ∈ S) (j) : |(z j:ℝ)| ≤ X^w := by
    calc
      _ ≤ Cbox*X^(ω j) := hbox z hz j
      _ ≤ X*X^(∑ l, ω l) := mul_le_mul hCX (Real.rpow_le_rpow_of_exponent_le hX1 (hmax j))
        (Real.rpow_nonneg hXp.le _) (by linarith)
      _ = X^w := by dsimp [w]; rw [Real.rpow_add hXp,Real.rpow_one]
  let G : KernelGeometry 3 := ⟨S,X^w,Real.one_le_rpow hX1 hwpos,hbound⟩
  have hpoints : ∀ z ∈ G.points, q_64 I z := by
    intro z hz
    change I ≤ RingHom.ker (MvPolynomial.aeval (fun j => (z j:ℂ))).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = F := Set.mem_singleton_iff.mp hp
    subst p
    change MvPolynomial.aeval (fun j => (z j:ℂ)) (q_46 fc k) = 0
    have hev : MvPolynomial.aeval (fun j => (z j:ℂ)) (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) fc) = fc.eval (z 0:ℂ) := by
      induction fc using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,Polynomial.eval_add,hp,hq]
      | monomial n a => simp [Polynomial.eval₂_monomial,Polynomial.eval_monomial]
    simpa only [q_46,map_sub,map_mul,map_pow,MvPolynomial.aeval_X,hev,sub_eq_zero] using heq z hz
  have hh := hcount X hXcut G le_rfl hbox I hI hdI.le heI.le hpoints
  have hend := hh (by
    intro i e J hJ hIJ _ hJe hJdim _
    let : J.IsPrime := hJ
    fin_cases i
    · have heJI : I = J := q_404 I J hIJ hdI hJdim
      subst J
      right
      intro T hT
      have hlo := hHs T hT
      have hn : 0 ≤ 2*(ω 1+ω 2+1)*T := by
        exact mul_nonneg (by linarith [hω 1,hω 2]) (by linarith)
      norm_num [dv,cc]
      linarith only [hlo,hn]
    · have hjdim : q_0 J ≤ 1 := by simpa using hJdim.le
      have hS' : ∀ z ∈ S.filter (q_64 J), z ∈ S := fun z hz => (Finset.mem_filter.mp hz).1
      have hcur := hcurve e X hX2.le (S.filter (q_64 J)) (hinj.mono (Finset.filter_subset _ _))
        (fun z hz j => hbox z (hS' z hz) j) (fun z hz => hrange z (hS' z hz))
        (fun z hz => hselected z (hS' z hz)) J hJ hjdim hJe
        (fun z hz => (Finset.mem_filter.mp hz).2) (q_428 fc k J hIJ)
      rcases hcur with hsmall | hH
      · exact Or.inl hsmall
      · right
        intro T hT
        have hlo := hH T hT
        have hn : 0 ≤ Cs := hCs
        norm_num [dv,cc]
        linarith only [hlo,hn])
  have hexp : (∑ i : Fin 2, ((2-i.val:ℕ):ℝ)*av i)+ε = δ+1/2+ε := by
    simp [av,Fin.sum_univ_two]
    ring
  simpa only [hexp] using hend
end QuarticPowerFree
end OAI
end
section
namespace OAI
namespace QuarticPowerFree
open scoped BigOperators
theorem q_283 (f : Polynomial ℤ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (n : ℤ), 0 ≤ n → (n:ℝ) ≤ 2*X →
      |((f.eval n:ℤ):ℝ)| ≤ C*X^(f.natDegree:ℝ) := by
  classical
  let A : ℝ := ∑ i ∈ f.support, |(f.coeff i:ℝ)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let C := 2+A*2^f.natDegree
  have hC : 2 ≤ C := by dsimp [C]; nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) f.natDegree]
  refine ⟨C,hC,fun X hX n hn hnX => ?_⟩
  have hXp : 0 ≤ X := by linarith
  have hn' : 0 ≤ (n:ℝ) := by exact_mod_cast hn
  have hh : |((f.eval n:ℤ):ℝ)| ≤ A*(2*X)^f.natDegree := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
    push_cast
    calc
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)*(n:ℝ)^i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)| *(2*X)^f.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_pow,abs_of_nonneg hn']
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (pow_le_pow_left₀ hn' hnX i).trans (pow_le_pow_right₀ (by linarith)
          (Polynomial.le_natDegree_of_mem_supp i hi))
      _ = A*(2*X)^f.natDegree := by rw [Finset.sum_mul]
  rw [mul_pow] at hh
  rw [Real.rpow_natCast]
  have hc : A*2^f.natDegree ≤ C := by dsimp [C]; linarith
  exact hh.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (pow_nonneg hXp _))
theorem q_138 (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    Squarefree (f.map (Int.castRingHom ℂ)) := by
  have h := hf.separable.map (f := Rat.castHom ℂ)
  have he : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by ext; simp
  rw [Polynomial.map_map,he] at h
  exact h.squarefree
theorem q_201 (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 2 ≤ f.natDegree) (n : ℤ) :
    f.eval n ≠ 0 := by
  intro hz
  have hr : (f.map (Int.castRingHom ℚ)).IsRoot (n:ℚ) := by
    change (f.map (Int.castRingHom ℚ)).eval (n:ℚ) = 0
    rw [Polynomial.eval_intCast_map]
    change (Int.castRingHom ℚ) (f.eval n) = 0
    rw [hz,map_zero]
  have hdvd := Polynomial.dvd_iff_isRoot.mpr hr
  have hu : ¬ IsUnit (Polynomial.X-Polynomial.C (n:ℚ)) := by
    exact Polynomial.not_isUnit_of_natDegree_pos _ (by rw [Polynomial.natDegree_X_sub_C]; decide)
  have ha := (hf.dvd_iff.mp hdvd).resolve_left hu
  have he := Polynomial.natDegree_le_of_dvd ha.dvd (Polynomial.X_sub_C_ne_zero (n:ℚ))
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_X_sub_C] at he
  omega
theorem q_449 {C X : ℝ} (hC : 2 ≤ C) (hX : 1 ≤ X)
    {d k : ℕ} (hd : 9 ≤ d) (hk : k = d-2)
    (y : ℤ) (p : ℕ) (hp : X < p)
    (hv : |(y:ℝ)| *(p:ℝ)^k ≤ C*X^(d:ℝ))
    (hy : y ≠ 0) :
    (|(y:ℝ)| ≤ C*X^(2:ℝ) ∧ (p:ℝ) ≤ C*X^(11/10:ℝ)) ∨
    (|(y:ℝ)| ≤ C*X^(13/10:ℝ) ∧ (p:ℝ) ≤ C*X^(13/10:ℝ)) := by
  have hXp : 0 < X := by linarith
  have hpp : (0:ℝ) < p := by linarith
  have hk0 : 0 < k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk0
  have hdR : (9:ℝ) ≤ d := by exact_mod_cast hd
  have hdk : (d:ℝ) = (k:ℝ)+2 := by exact_mod_cast (show d=k+2 by omega)
  have hy1 : 1 ≤ |(y:ℝ)| := by exact_mod_cast (Int.one_le_abs hy)
  have hCp : 0 < C := by linarith
  have hpow : (p:ℝ)^k ≤ C*X^(d:ℝ) := by nlinarith [pow_pos hpp k]
  have hprime : (p:ℝ) ≤ C*X^(13/10:ℝ) := by
    apply (Real.rpow_le_rpow_iff hpp.le (by positivity) hkR).mp
    simp only [Real.rpow_natCast]
    rw [mul_pow,← Real.rpow_natCast (X^(13/10:ℝ)) k,← Real.rpow_mul hXp.le]
    have hexp : (d:ℝ) ≤ 13/10*(k:ℝ) := by linarith
    have hCC : C ≤ C^k := le_self_pow₀ (by linarith) hk0.ne'
    exact hpow.trans (mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hX hexp)
      (Real.rpow_nonneg hXp.le _) (by positivity))
  by_cases hpbox : (p:ℝ) ≤ X^(11/10:ℝ)
  · left
    refine ⟨?_,hpbox.trans (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (by linarith))⟩
    have hxk : X^(k:ℝ) ≤ (p:ℝ)^k := by rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hXp.le hp.le k
    have he : C*X^(d:ℝ) = (C*X^(2:ℝ))*X^(k:ℝ) := by
      rw [hdk,Real.rpow_add hXp]; ring
    have hv' := (mul_le_mul_of_nonneg_left hxk (abs_nonneg (y:ℝ))).trans hv
    rw [he] at hv'
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp _)).mp hv'
  · right
    refine ⟨?_,hprime⟩
    have hpbox' : X^(11/10:ℝ) ≤ (p:ℝ) := (lt_of_not_ge hpbox).le
    have hxk : X^((11/10:ℝ)*(k:ℝ)) ≤ (p:ℝ)^k := by
      rw [Real.rpow_mul hXp.le,Real.rpow_natCast]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hpbox' k
    have hexp : (d:ℝ) ≤ 13/10+11/10*(k:ℝ) := by linarith
    have he : C*X^(d:ℝ) ≤ (C*X^(13/10:ℝ))*X^((11/10:ℝ)*(k:ℝ)) := by
      rw [mul_assoc,← Real.rpow_add hXp]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) hCp.le
    have hv' := (mul_le_mul_of_nonneg_left hxk (abs_nonneg (y:ℝ))).trans (hv.trans he)
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp _)).mp hv'
section
open scoped BigOperators Classical
theorem q_338 (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin 3 → ℤ),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p) →
      (∀ z ∈ S, f.eval (z 0) = z 1*(z 2)^(f.natDegree-2)) →
      (S.card:ℝ) ≤ C*X^(1-1/2000:ℝ) := by
  classical
  let k := f.natDegree-2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hsq := q_138 f hirr
  obtain ⟨Cb,hCb,hpoly⟩ := q_283 f
  let ω₁ : Fin 3 → ℝ := ![1,2,11/10]
  let ω₂ : Fin 3 → ℝ := ![1,13/10,13/10]
  have hω₁ : ∀ j, 0 < ω₁ j := by intro j; fin_cases j <;> norm_num [ω₁]
  have hω₂ : ∀ j, 0 < ω₂ j := by intro j; fin_cases j <;> norm_num [ω₂]
  have hw₁ : ∀ j, (q_15 10 20 11 j:ℝ) = (10:ℝ)*ω₁ j := by
    intro j; fin_cases j <;> norm_num [q_15,ω₁]
  have hw₂ : ∀ j, (q_15 10 13 13 j:ℝ) = (10:ℝ)*ω₂ j := by
    intro j; fin_cases j <;> norm_num [q_15,ω₂]
  have hd' : (9:ℝ) ≤ f.natDegree := by exact_mod_cast hd
  have hm₁ : (20:ℝ)*11 ≤ (f.natDegree:ℝ)*(10:ℝ)^2*(499/1000:ℝ)^2 := by nlinarith
  have hm₂ : (13:ℝ)*13 ≤ (f.natDegree:ℝ)*(10:ℝ)^2*(499/1000:ℝ)^2 := by nlinarith
  obtain ⟨C₁,X₁,hC₁,hcount₁⟩ := q_128 f hf hsq k hk
    (a := 10) (b := 20) (c := 11) (by norm_num) (by norm_num) (by norm_num)
    ω₁ hω₁ rfl hw₁ (499/1000) (by norm_num) (by norm_num) hm₁ Cb (by linarith)
    (1/2000) (by norm_num)
  obtain ⟨C₂,X₂,hC₂,hcount₂⟩ := q_128 f hf hsq k hk
    (a := 10) (b := 13) (c := 13) (by norm_num) (by norm_num) (by norm_num)
    ω₂ hω₂ rfl hw₂ (499/1000) (by norm_num) (by norm_num) hm₂ Cb (by linarith)
    (1/2000) (by norm_num)
  refine ⟨C₁+C₂,max 1 (max X₁ X₂),by linarith,?_⟩
  intro X hX S hinj hrange hprime heq
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX₁ : X₁ < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hX
  have hX₂ : X₂ < X := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hX
  let B₁ := fun z : Fin 3 → ℤ => ∀ j, |(z j:ℝ)| ≤ Cb*X^(ω₁ j)
  let B₂ := fun z : Fin 3 → ℤ => ∀ j, |(z j:ℝ)| ≤ Cb*X^(ω₂ j)
  have hcover : ∀ z ∈ S, B₁ z ∨ B₂ z := by
    intro z hz
    obtain ⟨p,hp,hzp,hXp⟩ := hprime z hz
    have hz0 : 0 ≤ z 0 := by exact_mod_cast (show (0:ℝ) ≤ z 0 by linarith [(hrange z hz).1])
    have hb := hpoly X hX1.le (z 0) hz0 (hrange z hz).2
    have hev : ((f.eval (z 0):ℤ):ℝ) = (z 1:ℝ)*(p:ℝ)^k := by
      have hh := congrArg (fun a : ℤ => (a:ℝ)) (heq z hz)
      simpa only [Int.cast_mul,Int.cast_pow,hzp,Int.cast_natCast] using hh
    have hv : |(z 1:ℝ)| *(p:ℝ)^k ≤ Cb*X^(f.natDegree:ℝ) := by
      rw [hev,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ (p:ℝ)^k from pow_nonneg (Nat.cast_nonneg p) k)] at hb
      exact hb
    have hy : z 1 ≠ 0 := by
      intro hy
      have hh := heq z hz
      rw [hy,zero_mul] at hh
      exact q_201 f hirr (by omega) (z 0) hh
    have hb0 : |(z 0:ℝ)| ≤ Cb*X := by
      rw [abs_of_nonneg (by exact_mod_cast hz0)]
      exact (hrange z hz).2.trans (mul_le_mul_of_nonneg_right hCb (by linarith))
    rcases q_449 hCb hX1.le hd rfl (z 1) p hXp hv hy with h₁ | h₂
    · left
      intro j
      fin_cases j
      · simpa [ω₁,Real.rpow_one] using hb0
      · change |(z 1:ℝ)| ≤ Cb*X^(2:ℝ)
        exact h₁.1
      · change |(z 2:ℝ)| ≤ Cb*X^(11/10:ℝ)
        rw [hzp,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg p)]
        exact h₁.2
    · right
      intro j
      fin_cases j
      · simpa [ω₂,Real.rpow_one] using hb0
      · change |(z 1:ℝ)| ≤ Cb*X^(13/10:ℝ)
        exact h₂.1
      · change |(z 2:ℝ)| ≤ Cb*X^(13/10:ℝ)
        rw [hzp,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg p)]
        exact h₂.2
  have hselected : ∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0) := by
    intro z hz
    obtain ⟨p,hp,hzp,hXp⟩ := hprime z hz
    refine ⟨p,hp,hzp,hXp,?_⟩
    rw [heq z hz,hzp]
    exact dvd_mul_of_dvd_right (dvd_pow_self (p:ℤ) (by omega)) _
  have hcomplex : ∀ z ∈ S, (f.map (Int.castRingHom ℂ)).eval (z 0:ℂ) =
      (z 1:ℂ)*(z 2:ℂ)^k := by
    intro z hz
    rw [Polynomial.eval_intCast_map]
    change (((f.eval (z 0):ℤ):ℂ)) = (z 1:ℂ)*(z 2:ℂ)^k
    exact_mod_cast heq z hz
  have hc₁ := hcount₁ X hX₁ (S.filter B₁) (hinj.mono (Finset.filter_subset _ _))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hrange z (Finset.mem_filter.mp hz).1)
    (fun z hz => hselected z (Finset.mem_filter.mp hz).1)
    (fun z hz => hcomplex z (Finset.mem_filter.mp hz).1)
  have hc₂ := hcount₂ X hX₂ (S.filter B₂) (hinj.mono (Finset.filter_subset _ _))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hrange z (Finset.mem_filter.mp hz).1)
    (fun z hz => hselected z (Finset.mem_filter.mp hz).1)
    (fun z hz => hcomplex z (Finset.mem_filter.mp hz).1)
  have hsub : S ⊆ (S.filter B₁) ∪ (S.filter B₂) := by
    intro z hz
    rcases hcover z hz with h₁ | h₂
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h₁⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h₂⟩)
  have hcard : (S.card:ℝ) ≤ ((S.filter B₁).card:ℝ)+((S.filter B₂).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  norm_num at hc₁ hc₂ ⊢
  nlinarith only [hcard,hc₁,hc₂]
end
open Filter
open scoped Topology Classical
theorem high_degree_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) M:ℝ) ≤ C*(M:ℝ)^(1-1/2000:ℝ) := by
  classical
  obtain ⟨C,X₀,hC,hcount⟩ := q_338 f hf hirr hd
  refine ⟨C,hC,?_⟩
  have hlim : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop X₀)] with M hM
  let D := (Finset.Ioc M (2*M)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ M < p ∧ (p:ℤ)^(f.natDegree-2) ∣ f.eval (n:ℤ)
  have hD (n : D) : ∃ p : ℕ, p.Prime ∧ M < p ∧
      (p:ℤ)^(f.natDegree-2) ∣ f.eval (n.val:ℤ) := (Finset.mem_filter.mp n.property).2
  choose p hp hMp hdiv using hD
  choose y hy using hdiv
  let z := fun n : D => (![(n.val:ℤ),y n,(p n:ℤ)] : Fin 3 → ℤ)
  have hzinj : Function.Injective z := by
    intro u v huv
    apply Subtype.ext
    have hh := congrFun huv 0
    dsimp only [z,Matrix.cons_val_zero] at hh
    exact_mod_cast hh
  let S := Finset.univ.image z
  have hS : ∀ u ∈ S, ∃ n : D, z n = u := by
    intro u hu
    obtain ⟨n,_,hn⟩ := Finset.mem_image.mp hu
    exact ⟨n,hn⟩
  have hinj : Set.InjOn (fun u : Fin 3 → ℤ => u 0) (S:Set _) := by
    intro u hu v hv huv
    obtain ⟨i,rfl⟩ := hS u hu
    obtain ⟨j,rfl⟩ := hS v hv
    have hij : i = j := by
      apply Subtype.ext
      dsimp only [z,Matrix.cons_val_zero] at huv
      exact_mod_cast huv
    rw [hij]
  have hrange : ∀ u ∈ S, (M:ℝ) < (u 0:ℝ) ∧ (u 0:ℝ) ≤ 2*(M:ℝ) := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    have hn := Finset.mem_Ioc.mp (Finset.mem_filter.mp n.property).1
    dsimp only [z,Matrix.cons_val_zero]
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  have hprime : ∀ u ∈ S, ∃ q : ℕ, q.Prime ∧ u 2 = q ∧ (M:ℝ) < q := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    exact ⟨p n,hp n,rfl,by exact_mod_cast hMp n⟩
  have heq : ∀ u ∈ S, f.eval (u 0) = u 1*(u 2)^(f.natDegree-2) := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    change f.eval (n.val:ℤ) = y n*(p n:ℤ)^(f.natDegree-2)
    rw [hy n,mul_comm]
  have hc := hcount M hM S hinj hrange hprime heq
  have hcard : S.card = D.card := by
    rw [Finset.card_image_of_injective _ hzinj,Finset.card_univ,Fintype.card_coe]
  simpa only [hcard,dyadicTailCount,D] using hc
end QuarticPowerFree
end OAI
end
open Filter
open scoped Classical Topology
namespace Erdos978Determinant
lemma q_431 (P : ℕ → Prop) (N : ℕ) :
    ((Finset.Ico N (2 * N)).filter P).card ≤ ((Finset.Ioc N (2 * N)).filter P).card + 1 := by
  classical
  apply (Finset.card_le_card ?_).trans (Finset.card_insert_le N ((Finset.Ioc N (2 * N)).filter P))
  intro n hn
  obtain ⟨hI, hP⟩ := Finset.mem_filter.mp hn
  obtain ⟨hl, hh⟩ := Finset.mem_Ico.mp hI
  by_cases h : n = N
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hh.le⟩, hP⟩))
lemma q_330 (b : ℕ → ℕ) (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (h : ∀ᶠ n : ℕ in atTop, (b n : ℝ) ≤ C * (n : ℝ) ^ (1 - δ)) (A : ℕ) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, A * (b n + 1) < n := by
  have hzero : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hden : 0 < (2 : ℝ) * A * C := by positivity
  have small := hzero.eventually_lt_const (by positivity : 0 < 1 / ((2 : ℝ) * A * C))
  apply eventually_atTop.mp
  filter_upwards [h, small, eventually_gt_atTop (2 * A)] with n hb hsmall hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) ^ (1 - δ) = n * (n : ℝ) ^ (-δ) := by
    rw [sub_eq_add_neg, Real.rpow_add hnpos, Real.rpow_one]
  rw [hpow] at hb
  have hsmall' := (lt_div_iff₀ hden).mp hsmall
  have hb' : 2 * (A : ℝ) * b n < n := calc
    _ ≤ 2 * (A : ℝ) * (C * (n * (n : ℝ) ^ (-δ))) := by gcongr
    _ = (n : ℝ) * ((n : ℝ) ^ (-δ) * (2 * (A : ℝ) * C)) := by ring
    _ < (n : ℝ) * 1 := mul_lt_mul_of_pos_left hsmall' hnpos
    _ = _ := mul_one _
  have hbNat : 2 * A * b n < n := by exact_mod_cast hb'
  nlinarith only [hbNat, hn]
end Erdos978Determinant
open Erdos978Determinant Polynomial in
theorem h2_h2_h2_proof : OMA.E978R3.H2 := by
  intro f hi hd
  dsimp only
  intro A hA
  have hprim := hi.isPrimitive (by omega)
  have hrat := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hi
  obtain ⟨C, hC, hsave⟩ := OAI.QuarticPowerFree.high_degree_dyadic_tail f hprim hrat hd
  let k := f.natDegree - 2
  let P (N n : ℕ) := ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let b (N : ℕ) := ((Finset.Ioc N (2 * N)).filter (P N)).card
  have hcount : ∀ᶠ N : ℕ in atTop, (b N : ℝ) ≤ C * (N : ℝ) ^ (1 - 1 / 2000 : ℝ) := by
    simpa only [b, P, k, OAI.QuarticPowerFree.dyadicTailCount] using hsave
  obtain ⟨N₀, h₀⟩ := q_330 b C (1 / 2000) hC (by norm_num) hcount A hA
  refine ⟨N₀, fun N hN => ?_⟩
  exact (Nat.mul_le_mul_left A (q_431 (P N) N)).trans_lt (h₀ N hN)
end SL4

theorem OMA.solution : type_of% @Erdos978.erdos_978.variants.sub_two :=
  OMA.E978R1.main OMA.L1.h1_proof (OMA.E978R2.main OMA.L2.h2_h1_proof (OMA.E978R3.main OMA.L3.h2_h2_h1_proof h2_h2_h2_proof))
