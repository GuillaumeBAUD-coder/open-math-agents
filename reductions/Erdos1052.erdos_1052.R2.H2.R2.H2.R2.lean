import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2

/-!
# Large shift pairs on paths of largest children

In an exact fixed-core completion, a support child of a prime x is a support prime
dividing 1+x. If any shift has a pair above a threshold exceeding c+1, the
largest parent with such a pair lies on a path from a seed divisor which takes
the largest support child at every step. It suffices to examine the initial
sole-child segment and the segment following its first genuine fork.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H2_R2

/-- Bound pairs up to and including the first fork of each seed path. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      let edge := fun (x y : ℕ) => y ∈ S ∧ y ∣ 1 + x
      let sole := fun x y => edge x y ∧ ∀ z, edge x z → z = y
      ∀ t ∈ S, t ∣ 2 ^ a + 1 → ∀ q ∈ S, Relation.ReflTransGen sole t q →
        ∀ p r : ℕ, p.Prime → r.Prime → p * r ∣ 1 + q → min p r ≤ B

/-- Bound pairs strictly after the first fork, following only largest children. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      let edge := fun (x y : ℕ) => y ∈ S ∧ y ∣ 1 + x
      let sole := fun x y => edge x y ∧ ∀ z, edge x z → z = y
      let largest := fun x y => edge x y ∧ ∀ z, edge x z → z ≤ y
      ∀ t ∈ S, t ∣ 2 ^ a + 1 → ∀ f h q : ℕ, q ∈ S →
        Relation.ReflTransGen sole t f → largest f h →
        (∃ z, edge f z ∧ z ≠ h) → Relation.ReflTransGen largest h q →
        ∀ p r : ℕ, p.Prime → r.Prime → p * r ∣ 1 + q → min p r ≤ B

/-- Split a largest-child path at its first edge with a sibling. -/
theorem first_fork (edge : ℕ → ℕ → Prop) {t q : ℕ}
    (path : Relation.ReflTransGen (fun x y => edge x y ∧ ∀ z, edge x z → z ≤ y) t q) :
    Relation.ReflTransGen (fun x y => edge x y ∧ ∀ z, edge x z → z = y) t q ∨
    ∃ f h : ℕ,
      Relation.ReflTransGen (fun x y => edge x y ∧ ∀ z, edge x z → z = y) t f ∧
      (edge f h ∧ ∀ z, edge f z → z ≤ h) ∧ (∃ z, edge f z ∧ z ≠ h) ∧
      Relation.ReflTransGen (fun x y => edge x y ∧ ∀ z, edge x z → z ≤ y) h q := by
  induction path with
  | refl => exact Or.inl .refl
  | @tail x y path last ih =>
    rcases ih with solePath | ⟨f, h, solePath, fork, sibling, suffix⟩
    · by_cases unique : ∀ z, edge x z → z = y
      · exact Or.inl (solePath.tail ⟨last.1, unique⟩)
      · push Not at unique
        exact Or.inr ⟨x, y, solePath, last, unique, .refl⟩
    · exact Or.inr ⟨f, h, solePath, fork, sibling, suffix.tail last⟩

/-- A support prime beyond the fixed core's shifted prime powers is fed
by the seed or by a support shift. -/
theorem source_of_large_support {c a x : ℕ} {S : Finset ℕ} (hc : Odd c)
    (hx : x ∈ S) (hxp : x.Prime) (hxc : c + 1 < x)
    (bal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    x ∣ 2 ^ a + 1 ∨ ∃ y ∈ S, x ∣ 1 + y := by
  have hd := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hx) (2 * (2 ^ a * c))
  simp only [id_eq] at hd
  rw [← bal] at hd
  rcases hxp.dvd_mul.mp hd with hbase | hshift
  · obtain ⟨t, _, hxt⟩ := (hxp.prime.dvd_finsetProd_iff _).mp hbase
    have fac : (2 ^ a * c).factorization t =
        (if 2 = t then a else 0) + c.factorization t := by
      rw [Nat.factorization_mul (Nat.two_pow_pos a).ne' hc.pos.ne',
        Nat.prime_two.factorization_pow]
      simp only [Finsupp.add_apply, Finsupp.single_apply, eq_comm]
    by_cases ht : 2 = t
    · subst t
      have h2c : ¬ 2 ∣ c := by obtain ⟨k, hk⟩ := hc; omega
      rw [fac, if_pos rfl, Nat.factorization_eq_zero_of_not_dvd h2c, add_zero] at hxt
      exact Or.inl (by simpa only [Nat.add_comm 1] using hxt)
    · rw [fac, if_neg ht, zero_add] at hxt
      have hpow : t ^ c.factorization t ≤ c := Nat.ordProj_le t hc.pos.ne'
      have hxle := Nat.le_of_dvd (by omega : 0 < 1 + t ^ c.factorization t) hxt
      omega
  · exact Or.inr ((hxp.prime.dvd_finsetProd_iff _).mp hshift)

/-- A divisor greater than two of an odd prime's shift, itself odd, is smaller. -/
theorem odd_child_lt {x y : ℕ} (hx : 2 < x) (hxo : Odd x) (hyo : Odd y)
    (hd : x ∣ 1 + y) : x < y := by
  obtain ⟨k, hk⟩ := hd
  by_contra! hxy
  have hk2 : k < 2 := by
    by_contra! hh
    have := Nat.mul_le_mul_left x hh
    omega
  obtain ⟨i, hi⟩ := hxo
  obtain ⟨j, hj⟩ := hyo
  interval_cases k <;> simp_all
  omega

/-- A maximal offending parent is accessible from a seed root by repeatedly
taking largest children. The two prime factors of a shift may be equal. -/
theorem maximal_pair_path {S : Finset ℕ} {seed : ℕ → Prop} {q B : ℕ}
    (hq : q ∈ S) (hqB : B < q) (prime : ∀ x ∈ S, Nat.Prime x)
    (source : ∀ x ∈ S, B < x → seed x ∨ ∃ y ∈ S, x < y ∧ x ∣ 1 + y)
    (above : ∀ y ∈ S, q < y → ∀ p r : ℕ, p.Prime → r.Prime →
      p * r ∣ 1 + y → min p r ≤ B) :
    ∃ t ∈ S, seed t ∧ Relation.ReflTransGen
      (fun x y => (y ∈ S ∧ y ∣ 1 + x) ∧ ∀ z, (z ∈ S ∧ z ∣ 1 + x) → z ≤ y) t q := by
  let edge := fun x y => (y ∈ S ∧ y ∣ 1 + x) ∧
    ∀ z : ℕ, (z ∈ S ∧ z ∣ 1 + x) → z ≤ y
  have ascend (n : ℕ) : ∀ x ∈ S, q ≤ x → S.sup id - x = n →
      ∃ t ∈ S, seed t ∧ Relation.ReflTransGen edge t x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hqx hn
      rcases source x hx (by omega) with root | ⟨y, hy, hxy, hd⟩
      · exact ⟨x, hx, root, .refl⟩
      · have hybound : y ≤ S.sup id := Finset.le_sup (f := id) hy
        have hdist : S.sup id - y < n := by omega
        obtain ⟨t, ht, hs, path⟩ := ih _ hdist y hy (by omega) rfl
        refine ⟨t, ht, hs, path.tail ⟨⟨hx, hd⟩, ?_⟩⟩
        intro z hz
        by_contra! hxz
        have cop := (Nat.coprime_primes (prime x hx) (prime z hz.1)).mpr hxz.ne
        have pair := cop.mul_dvd_of_dvd_of_dvd hd hz.2
        have bound := above y hy (by omega) x z (prime x hx) (prime z hz.1) pair
        omega
  exact ascend _ q hq le_rfl rfl

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R2.H2 := by
  classical
  intro h₁ h₂ c hc hpow
  obtain ⟨B₁, hfirst⟩ := h₁ c hc hpow
  obtain ⟨B₂, hlater⟩ := h₂ c hc hpow
  let B := max (c + 1) (max 2 (max B₁ B₂))
  have hBc : c + 1 ≤ B := by dsimp [B]; omega
  have hB2 : 2 ≤ B := by dsimp [B]; omega
  refine ⟨B, ?_⟩
  intro a S
  dsimp only
  intro ha hcard hsub hpr bal q hq p r hp hr hd
  by_contra! hbad
  let bad := S.filter (fun y => ∃ i j : ℕ, i.Prime ∧ j.Prime ∧ i*j ∣ 1+y ∧ B < min i j)
  have hqbad : q ∈ bad := Finset.mem_filter.mpr ⟨hq, p, r, hp, hr, hd, hbad⟩
  have nonempty : bad.Nonempty := ⟨q, hqbad⟩
  let m := bad.max' nonempty
  obtain ⟨hm, i, j, hi, hj, hpair, hijB⟩ := Finset.mem_filter.mp (bad.max'_mem nonempty)
  have hmB : B < m := by
    have hle := Nat.le_of_dvd (by omega : 0 < 1 + m) hpair
    have hmul := Nat.mul_le_mul_left i hj.two_le
    omega
  have above (y : ℕ) (hy : y ∈ S) (hmy : m < y) (i j : ℕ) (hi : i.Prime)
      (hj : j.Prime) (hd : i*j ∣ 1+y) : min i j ≤ B := by
    by_contra! hn
    have hmem : y ∈ bad := Finset.mem_filter.mpr ⟨hy, i, j, hi, hj, hd, hn⟩
    exact hmy.not_ge (Finset.le_max' bad y hmem)
  have oddS (x : ℕ) (hx : x ∈ S) : Odd x :=
    (hpr x hx).1.odd_of_ne_two (by have := (Finset.mem_Icc.mp (hsub hx)).1; omega)
  have source (x : ℕ) (hx : x ∈ S) (hBx : B < x) :
      x ∣ 2 ^ a + 1 ∨ ∃ y ∈ S, x < y ∧ x ∣ 1 + y := by
    rcases source_of_large_support hc hx (hpr x hx).1 (by omega) bal with
      root | ⟨y, hy, hxy⟩
    · exact Or.inl root
    · exact Or.inr ⟨y, hy, odd_child_lt (by omega) (oddS x hx) (oddS y hy) hxy, hxy⟩
  obtain ⟨t, ht, hseed, path⟩ :=
    maximal_pair_path (seed := fun x => x ∣ 2 ^ a + 1) hm hmB
      (fun x hx => (hpr x hx).1) source above
  rcases first_fork (fun x y => y ∈ S ∧ y ∣ 1 + x) path with single |
      ⟨f, h, solePath, fork, sibling, suffix⟩
  · have bound := hfirst a S ha hcard hsub hpr bal t ht hseed m hm single i j hi hj hpair
    dsimp [B] at hijB
    omega
  · have bound := hlater a S ha hcard hsub hpr bal t ht hseed f h m hm solePath
      fork sibling suffix i j hi hj hpair
    dsimp [B] at hijB
    omega

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H2_R2

