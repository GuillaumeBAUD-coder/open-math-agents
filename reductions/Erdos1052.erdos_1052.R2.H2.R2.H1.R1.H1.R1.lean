import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1

/-!
For a fixed odd core c, remove its unitary divisor sum from the balance.
The remaining components are the power of two and the simple odd primes.
Their shifted product divided by their product is a fixed rational number.
An elementary argument for lists, including repeated entries, settles every
bounded support. Nielsen's rational product bound for distinct entries also
applies to the components of the unitary-perfect completion. The unitary
divisor product formula is due to Subbarao and Warren.

Write t for the exponent of 2 in a. The Fermat number F = 2^(2^t)+1
divides the seed 2^a+1. One remaining question concerns a seed pair that
meets F at unbounded t. The other concerns seed primes outside F, which
must divide the cofactor. Both questions apply only to large simple supports.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1_H1_R1

/-- Large simple supports, large 2-adic depth, and a pair meeting the
Fermat factor. One prime divides that factor and the other divides the seed. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ q ∈ c.primeFactors, 2 ≤ c.factorization q) →
    ∃ K T D : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
      5 ≤ a → 4 ≤ S.card → K < S.card → T < padicValNat 2 a → S ⊆ Finset.Icc 3 u →
      (∀ q ∈ S, q.Prime ∧ ¬ q ∣ b) →
      u * (∏ q ∈ S, (1 + q)) = (2 * b) * (∏ q ∈ S, q) →
      ∀ p ∈ S, ∀ r ∈ S, p ≠ r → p ∣ 2 ^ (2 ^ padicValNat 2 a) + 1 →
        r ∣ 2 ^ a + 1 → min p r ≤ D

/-- On large simple supports, the part of the seed cofactor outside the
Fermat factor has at most one support prime above a fixed cutoff. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ q ∈ c.primeFactors, 2 ≤ c.factorization q) →
    ∃ K D : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
      5 ≤ a → 4 ≤ S.card → K < S.card → S ⊆ Finset.Icc 3 u →
      (∀ q ∈ S, q.Prime ∧ ¬ q ∣ b) →
      u * (∏ q ∈ S, (1 + q)) = (2 * b) * (∏ q ∈ S, q) →
      (S.filter (fun q => D < q ∧
        q ∣ (2 ^ a + 1) / (2 ^ (2 ^ padicValNat 2 a) + 1) ∧
        ¬ q ∣ 2 ^ (2 ^ padicValNat 2 a) + 1)).card ≤ 1

/-- The relative excess of the shifted product is controlled by its smallest entry. -/
theorem product_estimate (m : ℕ) (X : List ℕ)
    (hm : ∀ x ∈ X, m ≤ x) (positive : ∀ x ∈ X, 0 < x) :
    m * (X.map (fun x => 1 + x)).prod ≤ (m + 3 ^ X.length) * X.prod := by
  induction X with
  | nil => simp
  | cons y Y ih =>
    have hy : m ≤ y := hm y (by simp)
    have yp : 0 < y := positive y (by simp)
    have rest := ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      (fun x hx => positive x (List.mem_cons_of_mem _ hx))
    let V := 3 ^ Y.length
    have vp : 0 < V := by dsimp [V]; positivity
    have error : m + V ≤ 2 * V * y := calc
      m + V ≤ y + V := Nat.add_le_add_right hy V
      _ ≤ V*y + V*y := Nat.add_le_add (Nat.le_mul_of_pos_left y vp) (Nat.le_mul_of_pos_right V yp)
      _ = 2 * V * y := by ring
    have factor : (1+y) * (m+V) ≤ (m+3*V)*y := by nlinarith only [error]
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    change m * ((1+y) * (Y.map (fun x => 1+x)).prod) ≤ (m+V*3)*(y*Y.prod)
    calc
      _ = (1+y) * (m * (Y.map (fun x => 1+x)).prod) := by ring
      _ ≤ (1+y) * ((m+V)*Y.prod) := Nat.mul_le_mul_left _ rest
      _ = ((1+y)*(m+V))*Y.prod := by ring
      _ ≤ ((m+3*V)*y)*Y.prod := Nat.mul_le_mul_right _ factor
      _ = _ := by ring

theorem product_le_shift (X : List ℕ) :
    X.prod ≤ (X.map (fun x => 1+x)).prod := by
  induction X with
  | nil => simp
  | cons x X ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_le_mul (by omega) ih

theorem minimum_bound {P Q m : ℕ} {X : List ℕ}
    (hP : 0 < P) (mem : m ∈ X) (least : ∀ x ∈ X, m ≤ x)
    (positive : ∀ x ∈ X, 0 < x)
    (balance : P * (X.map (fun x => 1+x)).prod = Q * X.prod) :
    m ≤ P * 3 ^ X.length := by
  have denom : 0 < X.prod := List.prod_pos positive
  have strict : X.prod < (X.map (fun x => 1+x)).prod := by
    cases X with
    | nil => simp at mem
    | cons y Y =>
      have rest : 0 < Y.prod := List.prod_pos (fun x hx => positive x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.prod_cons]
      exact (Nat.mul_lt_mul_of_pos_right (show y < 1+y by omega) rest).trans_le
        (Nat.mul_le_mul_left _ (product_le_shift Y))
  have ratio : P < Q := by
    by_contra! h
    have lo := Nat.mul_lt_mul_of_pos_left strict hP
    have hi := Nat.mul_le_mul_right X.prod h
    omega
  have estimate := product_estimate m X least positive
  have cancel : m * Q ≤ P * (m + 3 ^ X.length) := by
    apply Nat.le_of_mul_le_mul_right _ denom
    calc
      (m*Q)*X.prod = m*(Q*X.prod) := by ring
      _ = P*(m*(X.map (fun x => 1+x)).prod) := by rw [← balance]; ring
      _ ≤ P*((m + 3 ^ X.length)*X.prod) := Nat.mul_le_mul_left P estimate
      _ = (P * (m + 3 ^ X.length))*X.prod := by ring
  have comparison := (Nat.mul_le_mul_left m (Nat.succ_le_of_lt ratio)).trans cancel
  nlinarith only [comparison]

/-- The bound can be chosen uniformly for all numerators P ≤ A and all Q. -/
theorem bounded_length (K A : ℕ) : ∃ M : ℕ,
    ∀ P Q : ℕ, 0 < P → P ≤ A → ∀ X : List ℕ, X.length ≤ K →
    (∀ x ∈ X, 0 < x) → P * (X.map (fun x => 1+x)).prod = Q * X.prod →
    ∀ x ∈ X, x ≤ M := by
  induction K generalizing A with
  | zero =>
    refine ⟨0, ?_⟩
    intro P Q hP hA X len pos bal x hx
    have : X = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this] at hx
  | succ K ih =>
    let L := A * 3 ^ (K+1)
    obtain ⟨M, peel⟩ := ih (A*(1+L))
    refine ⟨max L M, ?_⟩
    intro P Q hP hA X len pos bal x hx
    obtain ⟨m, hm, least⟩ := X.toFinset.exists_min_image id ⟨x, List.mem_toFinset.mpr hx⟩
    have member := List.mem_toFinset.mp hm
    have small : m ≤ L := (minimum_bound hP member
      (fun t ht => least t (List.mem_toFinset.mpr ht)) pos bal).trans
      (Nat.mul_le_mul hA (Nat.pow_le_pow_right (by decide : 0 < 3) len))
    let Y := X.erase m
    have perm : X.Perm (m :: Y) := List.perm_cons_erase member
    have remLen : Y.length ≤ K := by
      have h := perm.length_eq
      simp only [List.length_cons] at h
      omega
    have remPos : ∀ y ∈ Y, 0 < y :=
      fun y hy => pos y (perm.mem_iff.mpr (List.mem_cons_of_mem _ hy))
    have remBal : (P*(1+m)) * (Y.map (fun t => 1+t)).prod = (Q*m)*Y.prod := by
      have hp := (perm.map (fun t => 1+t)).prod_eq
      have hq := perm.prod_eq
      rw [hp,hq] at bal
      simp only [List.map_cons,List.prod_cons] at bal
      simpa only [Nat.mul_assoc] using bal
    rcases List.mem_cons.mp (perm.mem_iff.mp hx) with eq | tail
    · exact eq ▸ small.trans (Nat.le_max_left L M)
    · exact (peel _ _ (Nat.mul_pos hP (by omega)) (Nat.mul_le_mul hA (by omega))
        Y remLen remPos remBal x tail).trans (Nat.le_max_right L M)

/-- Removing the power of two leaves exactly the factors of the fixed odd core. -/
theorem split_core_sum {a c : ℕ} (ha : 0 < a) (hc : Odd c) :
    (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) =
      (1 + 2 ^ a) * ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q) := by
  have hne : ¬ 2 ∣ c := by obtain ⟨t, ht⟩ := hc; omega
  have hout : 2 ∉ c.primeFactors := fun h => hne (Nat.dvd_of_mem_primeFactors h)
  have h2pow : 2 ^ a ≠ 0 := (Nat.two_pow_pos a).ne'
  have hs : (2 ^ a * c).primeFactors = insert 2 c.primeFactors := by
    rw [Nat.primeFactors_mul h2pow hc.pos.ne', Nat.primeFactors_prime_pow ha.ne' Nat.prime_two]
    exact Finset.singleton_union ..
  have h2 : (2 ^ a * c).factorization 2 = a := by
    rw [Nat.factorization_mul h2pow hc.pos.ne', Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hne, Nat.add_zero]
  rw [hs, Finset.prod_insert hout, h2]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  have hq2 : q ≠ 2 := fun he => hout (he ▸ hq)
  rw [Nat.factorization_mul h2pow hc.pos.ne', Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_of_ne hq2, Nat.zero_add]

/-- The odd quotient of the exponent ensures that the base Fermat factor divides the seed. -/
theorem base_seed_dvd {a : ℕ} (ha : 0 < a) :
    2 ^ (2 ^ padicValNat 2 a) + 1 ∣ 2 ^ a + 1 := by
  have oddPart : Odd (Nat.divMaxPow a 2) := by
    apply Nat.not_even_iff_odd.mp
    intro evenPart
    exact Nat.not_dvd_divMaxPow (by decide : 1 < 2) ha.ne' (even_iff_two_dvd.mp evenPart)
  have h := oddPart.nat_add_dvd_pow_add_pow (2 ^ (2 ^ padicValNat 2 a)) 1
  simpa only [one_pow, ← pow_mul, Nat.pow_padicValNat_mul_divMaxPow] using h

/-- A prime divisor outside the base factor must divide the integer cofactor. -/
theorem outside_dvd_cofactor {a p : ℕ} (ha : 0 < a) (hp : p.Prime)
    (seed : p ∣ 2 ^ a + 1) (outside : ¬ p ∣ 2 ^ (2 ^ padicValNat 2 a) + 1) :
    p ∣ (2 ^ a + 1) / (2 ^ (2 ^ padicValNat 2 a) + 1) := by
  have decomp := Nat.mul_div_cancel' (base_seed_dvd ha)
  rw [← decomp] at seed
  exact (hp.dvd_mul.mp seed).resolve_left outside

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1.H1 := by
  intro base outside c odd powerful
  obtain ⟨K₁, T, D₁, onBase⟩ := base c odd powerful
  obtain ⟨K₂, D₂, offBase⟩ := outside c odd powerful
  let K := max K₁ K₂
  let P := ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)
  have posP : 0 < P := Finset.prod_pos (fun q _ => by positivity)
  obtain ⟨M, components⟩ := bounded_length (K+1) P
  let D := max (max M D₂) (max D₁ (2 ^ (2 ^ T) + 1))
  refine ⟨D, ?_⟩
  intro a S b u ha hcard hsub primes balance p r primeP primeR pair hp hr distinct
  by_cases small : S.card ≤ K
  · let X := 2 ^ a :: S.toList
    have len : X.length ≤ K + 1 := by simpa [X] using small
    have positive : ∀ x ∈ X, 0 < x := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ Nat.two_pow_pos a
      · exact (primes x (Finset.mem_toList.mp h)).1.pos
    have eqn : P * (X.map (fun x => 1+x)).prod = (2*c) * X.prod := by
      dsimp only [b, u] at balance
      rw [split_core_sum (by omega) odd] at balance
      dsimp only [X, P]
      simp only [List.map_cons, List.prod_cons, Finset.prod_map_toList, Finset.prod_toList]
      convert balance using 1 <;> ac_rfl
    have subp : p ∈ X := List.mem_cons_of_mem _ (Finset.mem_toList.mpr hp)
    have bound := components P (2*c) posP (Nat.le_refl _) X len positive eqn p subp
    exact (min_le_left p r).trans (bound.trans ((le_max_left ..).trans (le_max_left ..)))
  · have large₁ : K₁ < S.card := (Nat.le_max_left K₁ K₂).trans_lt (Nat.lt_of_not_ge small)
    have large₂ : K₂ < S.card := (Nat.le_max_right K₁ K₂).trans_lt (Nat.lt_of_not_ge small)
    have first : p ∣ 2^a + 1 := (dvd_mul_right p r).trans pair
    have second : r ∣ 2^a + 1 := (dvd_mul_left r p).trans pair
    let F := 2 ^ (2 ^ padicValNat 2 a) + 1
    have meets (x y : ℕ) (hx : x ∈ S) (hy : y ∈ S) (ne : x ≠ y)
        (xf : x ∣ F) (ys : y ∣ 2^a+1) : min x y ≤ D := by
      by_cases deep : T < padicValNat 2 a
      · exact (onBase a S ha hcard large₁ deep hsub primes balance x hx y hy ne xf ys).trans
          ((le_max_left ..).trans (le_max_right ..))
      · have depth : padicValNat 2 a ≤ T := Nat.le_of_not_gt deep
        have cap : F ≤ 2^(2^T)+1 := Nat.add_le_add_right
          (Nat.pow_le_pow_right (by decide : 0 < 2)
            (Nat.pow_le_pow_right (by decide : 0 < 2) depth)) 1
        exact (min_le_left x y).trans ((Nat.le_of_dvd (by dsimp [F]; positivity) xf).trans
          (cap.trans ((le_max_right ..).trans (le_max_right ..))))
    by_cases pbase : p ∣ F
    · exact meets p r hp hr distinct pbase second
    by_cases rbase : r ∣ F
    · simpa only [min_comm] using meets r p hr hp distinct.symm rbase first
    have sparse := offBase a S ha hcard large₂ hsub primes balance
    let W := S.filter (fun q => D₂ < q ∧ q ∣ (2^a+1)/F ∧ ¬ q ∣ F)
    change W.card ≤ 1 at sparse
    have bound : min p r ≤ D₂ := by
      by_contra! h
      have pp : p ∈ W := Finset.mem_filter.mpr ⟨hp, (lt_min_iff.mp h).1,
        outside_dvd_cofactor (by omega) primeP first pbase, pbase⟩
      have rr : r ∈ W := Finset.mem_filter.mpr ⟨hr, (lt_min_iff.mp h).2,
        outside_dvd_cofactor (by omega) primeR second rbase, rbase⟩
      exact (not_lt_of_ge sparse) (Finset.one_lt_card.mpr ⟨p, pp, r, rr, distinct⟩)
    exact bound.trans ((le_max_right ..).trans (le_max_left ..))

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1_H1_R1
