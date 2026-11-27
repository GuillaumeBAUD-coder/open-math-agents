import OMAReductions.R_Erdos983_erdos_983_variants_erdos_straus_R1

/-! Adapted from @OrangeHeadz's path construction in the merged proof of
Erdős 983, part i. Extend the finite path to a function on naturals and
apply the lower bound with one fewer edge than vertices. -/
namespace OMA983

open Finset

/-- `π n` is admissible in the definition of `f`, so the defining set is nonempty. -/
theorem mem_set (k n : ℕ) (hk : Nat.primeCounting n < k) :
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = Nat.primeCounting n ∧ (∀ p ∈ S, p.Prime) ∧
        Nat.primeCounting n < Erdos983.numSmooth A S := by
  intro A hA hAk
  refine ⟨(Finset.range (n + 1)).filter Nat.Prime, ?_, ?_, ?_⟩
  · simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  · exact fun p hp => (Finset.mem_filter.mp hp).2
  · have hAll : A.filter (fun a => ∀ p ∈ a.primeFactors,
        p ∈ (Finset.range (n + 1)).filter Nat.Prime) = A := by
      refine Finset.filter_true_of_mem fun a ha p hp => ?_
      have ha' := Finset.mem_Icc.mp (hA ha)
      have hp' := Nat.mem_primeFactors.mp hp
      have hpa : p ≤ a := Nat.le_of_dvd (by omega) hp'.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp'.1⟩
    rw [Erdos983.numSmooth, hAll, hAk]
    exact hk

/-- A set `A` on which every small set of primes has few smooth elements bounds `f` below. -/
theorem f_ge (k n R : ℕ) (hk : Nat.primeCounting n < k) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hAk : A.card = k)
    (hbad : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → S.card < R →
      Erdos983.numSmooth A S ≤ S.card) : R ≤ Erdos983.f k n := by
  have hne : {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < Erdos983.numSmooth A S}.Nonempty :=
    ⟨Nat.primeCounting n, mem_set k n hk⟩
  have hmem : Erdos983.f k n ∈ {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < Erdos983.numSmooth A S} :=
    Nat.sInf_mem hne
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨S, hS, hprime, hgt⟩ := hmem A hA hAk
  have := hbad S hprime (by rw [hS]; exact hlt)
  omega

/-- The path construction: a path of `m + 1` distinct primes whose adjacent products are `≤ n`
forces `f (π n + 1) n ≥ m + 1`. -/
theorem path_lower (n m : ℕ) (v : ℕ → ℕ) (hm : 1 ≤ m)
    (hprime : ∀ j, j ≤ m → (v j).Prime)
    (hinj : ∀ i j, i ≤ m → j ≤ m → v i = v j → i = j)
    (hedge : ∀ j, j < m → v j * v (j + 1) ≤ n) :
    m + 1 ≤ Erdos983.f (Nat.primeCounting n + 1) n := by
  classical
  -- the pieces of the set
  set E : Finset ℕ := (Finset.range m).image (fun j => v j * v (j + 1)) with hE
  set I : Finset ℕ := (Finset.Ico 1 m).image v with hI
  set Pn : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime with hPn
  set Q : Finset ℕ := Pn \ I with hQ
  have hPncard : Pn.card = Nat.primeCounting n := by
    simp [hPn, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  -- edges are injective
  have hEinj : Set.InjOn (fun j => v j * v (j + 1)) (Finset.range m : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < m := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' : j < m := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    simp only at hij
    have pi0 := hprime i (by omega)
    have pi1 := hprime (i + 1) (by omega)
    have pj0 := hprime j (by omega)
    have pj1 := hprime (j + 1) (by omega)
    have d0 : v i ∣ v j * v (j + 1) := ⟨v (i + 1), hij.symm⟩
    have d1 : v (i + 1) ∣ v j * v (j + 1) := ⟨v i, by rw [← hij]; ring⟩
    have c0 : i = j ∨ i = j + 1 := by
      rcases pi0.dvd_mul.mp d0 with h | h
      · exact Or.inl (hinj i j (by omega) (by omega) ((Nat.prime_dvd_prime_iff_eq pi0 pj0).mp h))
      · exact Or.inr (hinj i (j + 1) (by omega) (by omega)
          ((Nat.prime_dvd_prime_iff_eq pi0 pj1).mp h))
    have c1 : i + 1 = j ∨ i + 1 = j + 1 := by
      rcases pi1.dvd_mul.mp d1 with h | h
      · exact Or.inl (hinj (i + 1) j (by omega) (by omega)
          ((Nat.prime_dvd_prime_iff_eq pi1 pj0).mp h))
      · exact Or.inr (hinj (i + 1) (j + 1) (by omega) (by omega)
          ((Nat.prime_dvd_prime_iff_eq pi1 pj1).mp h))
    omega
  have hEcard : E.card = m := by
    rw [hE, Finset.card_image_of_injOn hEinj, Finset.card_range]
  have hIcard : I.card ≤ m - 1 := by
    have := Finset.card_image_le (s := Finset.Ico 1 m) (f := v)
    rw [Nat.card_Ico] at this
    exact this
  have hQcard : Nat.primeCounting n - (m - 1) ≤ Q.card := by
    have h1 := Finset.le_card_sdiff I Pn
    rw [hPncard] at h1
    have h2 : Q.card = (Pn \ I).card := by rw [hQ]
    omega
  have hEQ : Disjoint E Q := by
    rw [Finset.disjoint_left]
    intro a haE haQ
    rw [hE, Finset.mem_image] at haE
    obtain ⟨j, hj, rfl⟩ := haE
    have hj' := Finset.mem_range.mp hj
    have hp : (v j * v (j + 1)).Prime := by
      rw [hQ, Finset.mem_sdiff, hPn, Finset.mem_filter] at haQ
      exact haQ.1.2
    exact Nat.not_prime_mul (hprime j (by omega)).one_lt.ne'
      (hprime (j + 1) (by omega)).one_lt.ne' hp
  -- the big set
  have hbig : Nat.primeCounting n + 1 ≤ (E ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hEQ, hEcard]
    omega
  have hsub0 : E ∪ Q ⊆ Finset.Icc 1 n := by
    intro a ha
    rw [Finset.mem_union] at ha
    rw [Finset.mem_Icc]
    rcases ha with ha | ha
    · rw [hE, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      have hj' := Finset.mem_range.mp hj
      have p0 := (hprime j (by omega)).pos
      have p1 := (hprime (j + 1) (by omega)).pos
      exact ⟨Nat.mul_pos p0 p1, hedge j hj'⟩
    · rw [hQ, Finset.mem_sdiff, hPn, Finset.mem_filter, Finset.mem_range] at ha
      have := ha.1.2.pos
      omega
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hbig
  apply f_ge (Nat.primeCounting n + 1) n (m + 1) (by omega) A (hAsub.trans hsub0) hAcard
  intro S hSprime hScard
  -- some path vertex is missing from `S`
  obtain ⟨t, htm, htS⟩ : ∃ t, t ≤ m ∧ v t ∉ S := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.range (m + 1)).image v ⊆ S := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact hcon j (by have := Finset.mem_range.mp hj; omega)
    have hcard : ((Finset.range (m + 1)).image v).card = m + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
      exact hinj i j (by omega) (by omega) hij
    have := Finset.card_le_card hsub
    omega
  -- smooth edge indices
  set J : Finset ℕ := (Finset.range m).filter (fun j => v j ∈ S ∧ v (j + 1) ∈ S) with hJ
  set h : ℕ → ℕ := fun j => if j < t then v (j + 1) else v j with hh
  have hJmem : ∀ j, j ∈ J → j < m ∧ v j ∈ S ∧ v (j + 1) ∈ S ∧ j ≠ t ∧ j + 1 ≠ t := by
    intro j hj
    rw [hJ, Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨hj.1, hj.2.1, hj.2.2, ?_, ?_⟩
    · intro e; rw [e] at hj; exact htS hj.2.1
    · intro e; rw [e] at hj; exact htS hj.2.2
  have hhinj : Set.InjOn h (J : Set ℕ) := by
    intro i hi j hj hij
    obtain ⟨hi1, -, -, hi4, hi5⟩ := hJmem i (Finset.mem_coe.mp hi)
    obtain ⟨hj1, -, -, hj4, hj5⟩ := hJmem j (Finset.mem_coe.mp hj)
    simp only [hh] at hij
    by_cases c1 : i < t <;> by_cases c2 : j < t
    · rw [if_pos c1, if_pos c2] at hij
      have := hinj (i + 1) (j + 1) (by omega) (by omega) hij
      omega
    · rw [if_pos c1, if_neg c2] at hij
      have := hinj (i + 1) j (by omega) (by omega) hij
      omega
    · rw [if_neg c1, if_pos c2] at hij
      have := hinj i (j + 1) (by omega) (by omega) hij
      omega
    · rw [if_neg c1, if_neg c2] at hij
      exact hinj i j (by omega) (by omega) hij
  -- the images are interior vertices lying in `S`
  have hhS : J.image h ⊆ S := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨-, h2, h3, -, -⟩ := hJmem j hj
    simp only [hh]
    by_cases c : j < t
    · rw [if_pos c]; exact h3
    · rw [if_neg c]; exact h2
  have hhI : J.image h ⊆ I := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨h1, -, -, h4, h5⟩ := hJmem j hj
    simp only [hh]
    rw [hI, Finset.mem_image]
    by_cases c : j < t
    · rw [if_pos c]
      exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
    · rw [if_neg c]
      exact ⟨j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  have hdisj : Disjoint (S ∩ Q) (J.image h) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := hhI hb
    rw [Finset.mem_inter, hQ, Finset.mem_sdiff] at ha
    exact ha.2.2 h1
  have hcount : (S ∩ Q).card + J.card ≤ S.card := by
    have e1 : (J.image h).card = J.card := Finset.card_image_of_injOn hhinj
    have e2 := Finset.card_union_of_disjoint hdisj
    have e3 : (S ∩ Q) ∪ J.image h ⊆ S :=
      Finset.union_subset Finset.inter_subset_left hhS
    have e4 := Finset.card_le_card e3
    omega
  -- count the smooth elements
  have hsmooth : (E ∪ Q).filter (fun a => ∀ p ∈ a.primeFactors, p ∈ S) ⊆
      J.image (fun j => v j * v (j + 1)) ∪ (S ∩ Q) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_union] at ha
    obtain ⟨ha1, ha2⟩ := ha
    rw [Finset.mem_union]
    rcases ha1 with ha1 | ha1
    · left
      rw [hE, Finset.mem_image] at ha1
      obtain ⟨j, hj, rfl⟩ := ha1
      have hj' := Finset.mem_range.mp hj
      have p0 := hprime j (by omega)
      have p1 := hprime (j + 1) (by omega)
      rw [Finset.mem_image]
      refine ⟨j, ?_, rfl⟩
      rw [hJ, Finset.mem_filter]
      refine ⟨hj, ha2 _ ?_, ha2 _ ?_⟩
      · exact Nat.mem_primeFactors.mpr ⟨p0, Dvd.intro _ rfl,
          Nat.mul_ne_zero p0.ne_zero p1.ne_zero⟩
      · exact Nat.mem_primeFactors.mpr ⟨p1, Dvd.intro_left _ rfl,
          Nat.mul_ne_zero p0.ne_zero p1.ne_zero⟩
    · right
      rw [Finset.mem_inter]
      refine ⟨?_, ha1⟩
      have hap : a.Prime := by
        rw [hQ, Finset.mem_sdiff, hPn, Finset.mem_filter] at ha1
        exact ha1.1.2
      exact ha2 a (Nat.mem_primeFactors.mpr ⟨hap, dvd_refl a, hap.ne_zero⟩)
  have hA0 : Erdos983.numSmooth (E ∪ Q) S ≤ S.card := by
    rw [Erdos983.numSmooth]
    have e1 := Finset.card_le_card hsmooth
    have e2 := Finset.card_union_le (J.image (fun j => v j * v (j + 1))) (S ∩ Q)
    have e3 := Finset.card_image_le (s := J) (f := fun j => v j * v (j + 1))
    omega
  have hAle : Erdos983.numSmooth A S ≤ Erdos983.numSmooth (E ∪ Q) S := by
    rw [Erdos983.numSmooth, Erdos983.numSmooth]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hAsub)
  omega
end OMA983

theorem OMA.solution : OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1.H1 := by
  intro n t ht q hq hp hEdge
  let v (i : ℕ) := if h : i < t then q ⟨i,h⟩ else 0
  have hv (i : ℕ) (hi : i < t) : v i = q ⟨i,hi⟩ := dif_pos hi
  have h := OMA983.path_lower n (t-1) v (by omega) (by
    intro j hj
    rw [hv j (by omega)]
    exact hp _) (by
    intro i j hi hj hij
    rw [hv i (by omega), hv j (by omega)] at hij
    exact congrArg Fin.val (hq hij)) (by
    intro j hj
    rw [hv j (by omega), hv (j+1) (by omega)]
    exact hEdge _ _ rfl)
  simpa only [Nat.sub_add_cancel (show 1 ≤ t by omega)] using h
