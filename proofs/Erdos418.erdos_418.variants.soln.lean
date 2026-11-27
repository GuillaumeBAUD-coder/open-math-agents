import FormalConjectures.ErdosProblems.«418»

-- Problem: Erdős Problem 418 — soln
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/418.lean:129 (declaration Erdos418.erdos_418.variants.soln)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.O13b

def T : ℕ := 1018406

def oddPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009]

def primeB (k n : ℕ) : Bool :=
  2 ≤ n && (List.range k).all (fun d => d < 2 || n < d * d || n % d != 0)

lemma primeB_of_prime (k n : ℕ) (hn : n.Prime) : primeB k n = true := by
  unfold primeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hn.two_le, fun d _ => ?_⟩
  by_cases h2 : d < 2
  · left; left; exact h2
  by_cases h3 : n < d * d
  · left; right; exact h3
  right
  intro hmod
  have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
  rcases hn.eq_one_or_self_of_dvd d hdvd with h | h
  · omega
  · subst h
    push Not at h3
    nlinarith

def nodeOK (r ph P : ℕ) : Bool :=
  T < ph || (T - ph) % (2 * r - ph) != 0 || (T - ph) / (2 * r - ph) ≤ P ||
    !primeB 1010 ((T - ph) / (2 * r - ph))

lemma nodeOK_sound (r ph P q : ℕ) (h : nodeOK r ph P = true) (hfr : 0 < 2 * r - ph)
    (hq : q.Prime) (hqP : P < q) (heq : q * (2 * r - ph) + ph = T) : False := by
  have h1 : T - ph = q * (2 * r - ph) := by omega
  have h2 : ¬ T < ph := by omega
  have h3 : (T - ph) % (2 * r - ph) = 0 := by rw [h1]; exact Nat.mul_mod_left _ _
  have h4 : (T - ph) / (2 * r - ph) = q := by rw [h1]; exact Nat.mul_div_cancel _ hfr
  have h5 := primeB_of_prime 1010 q hq
  unfold nodeOK at h
  rw [h3, h4, h5] at h
  simp at h
  omega

def sub : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | p :: L, r, ph => if T ≤ r * p * p then true else
      (nodeOK (r * p) (ph * (p - 1)) p && sub L (r * p) (ph * (p - 1)) && sub L r ph)

lemma prod_pos (S : List ℕ) (hS : ∀ s ∈ S, 1 ≤ s) : 0 < S.prod := by
  induction S with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons]
    have := hS a (by simp)
    have := ih (fun s hs => hS s (by simp [hs]))
    positivity

lemma sub_sound : ∀ (L : List ℕ) (r ph : ℕ), sub L r ph = true → L.Pairwise (· < ·) →
    (∀ s ∈ L, 1 ≤ s) → 0 < r → ph ≤ r →
    ∀ S : List ℕ, S.Sublist L → S ≠ [] → ∀ q : ℕ, q.Prime → (∀ s ∈ S, s < q) →
    r * S.prod * q < T →
    q * (2 * (r * S.prod) - ph * (S.map (fun s => s - 1)).prod) +
      ph * (S.map (fun s => s - 1)).prod = T → False := by
  intro L
  induction L with
  | nil =>
    intro r ph _ _ _ _ _ S hS hne
    exact absurd (List.sublist_nil.1 hS) hne
  | cons p L ih =>
    intro r ph h hsort hpos hr hph S hS hne q hq hSq hsize heq
    have hpL : ∀ s ∈ L, p < s := (List.pairwise_cons.1 hsort).1
    have hsortL : L.Pairwise (· < ·) := (List.pairwise_cons.1 hsort).2
    have hp1 : 1 ≤ p := hpos p (by simp)
    have hposL : ∀ s ∈ L, 1 ≤ s := fun s hs => hpos s (by simp [hs])
    have hSpos : ∀ s ∈ S, 1 ≤ s := fun s hs => hpos s (hS.subset hs)
    unfold sub at h
    split_ifs at h with hT
    · -- pruned: contradiction with the size bound
      obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S hne
      have hps : p ≤ s := by
        rcases List.mem_cons.1 (hS.subset hs) with h' | h'
        · omega
        · exact (hpL s h').le
      have hsq : s < q := hSq s hs
      have hsprod : s ≤ S.prod := Nat.le_of_dvd (prod_pos S hSpos) (List.dvd_prod hs)
      have e1 : r * p * p ≤ r * s * q := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left r hps) (by omega)
      have e2 : r * s * q ≤ r * S.prod * q :=
        Nat.mul_le_mul_right q (Nat.mul_le_mul_left r hsprod)
      omega
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hnode, hsub1⟩, hsub2⟩ := h
      cases hS with
      | cons _ hS' =>
        exact ih r ph hsub2 hsortL hposL hr hph S hS' hne q hq hSq hsize heq
      | cons_cons _ hS' =>
        rename_i S'
        have hpq : p < q := hSq p (by simp)
        by_cases hS'0 : S' = []
        · subst hS'0
          simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil] at heq
          refine nodeOK_sound (r * p) (ph * (p - 1)) p q hnode ?_ hq hpq heq
          have : ph * (p - 1) ≤ r * p := Nat.mul_le_mul hph (Nat.sub_le p 1)
          have : 0 < r * p := Nat.mul_pos hr hp1
          omega
        · refine ih (r * p) (ph * (p - 1)) hsub1 hsortL hposL (Nat.mul_pos hr hp1)
            (Nat.mul_le_mul hph (Nat.sub_le p 1)) S' hS' hS'0 q hq
            (fun s hs => hSq s (by simp [hs])) ?_ ?_
          · simp only [List.prod_cons] at hsize
            calc r * p * S'.prod * q = r * (p * S'.prod) * q := by ring
              _ < T := hsize
          · simp only [List.prod_cons, List.map_cons] at heq
            have e1 : r * (p * S'.prod) = r * p * S'.prod := by ring
            have e2 : ph * ((p - 1) * (S'.map (fun s => s - 1)).prod) =
                ph * (p - 1) * (S'.map (fun s => s - 1)).prod := by ring
            rw [e1, e2] at heq
            exact heq

lemma sub_check : sub oddPrimes 1 1 = true := by decide +kernel

lemma oddPrimes_sorted : oddPrimes.Pairwise (· < ·) := by decide +kernel

def complB : Bool :=
  (List.range 1010).all (fun n => n == 2 || !primeB 32 n || oddPrimes.contains n)

lemma complB_true : complB = true := by decide +kernel

lemma mem_oddPrimes (n : ℕ) (hn : n.Prime) (h2 : n ≠ 2) (h : n < 1010) : n ∈ oddPrimes := by
  have := complB_true
  unfold complB at this
  rw [List.all_eq_true] at this
  have h' := this n (List.mem_range.2 h)
  rw [primeB_of_prime 32 n hn] at h'
  simpa [h2] using h'

end OMA.O13b

namespace OMA.O13b

lemma prime_of_primeB (k n : ℕ) (h : primeB k n = true) (hk : n < k * k) : n.Prime := by
  unfold primeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  rw [pow_two] at hsq
  have hdk : n.minFac < k := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc hc
    omega
  rcases hall n.minFac hdk with (h | h) | h
  · have := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    omega
  · omega
  · exact h (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))

def allPB : Bool := oddPrimes.all (fun s => primeB 32 s && decide (s < 1024))

lemma allPB_true : allPB = true := by decide +kernel

lemma oddPrimes_prime (s : ℕ) (hs : s ∈ oddPrimes) : s.Prime := by
  have := allPB_true
  unfold allPB at this
  rw [List.all_eq_true] at this
  have h := this s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact prime_of_primeB 32 s h.1 (by omega)

lemma totient_sqf (r : ℕ) (hr : Squarefree r) :
    r.totient = ∏ p ∈ r.primeFactors, (p - 1) := by
  have h1 := Nat.totient_mul_prod_primeFactors r
  rw [Nat.prod_primeFactors_of_squarefree hr] at h1
  have hr0 : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  apply Nat.eq_of_mul_eq_mul_right hr0
  rw [h1, mul_comm]

lemma M_prime : Nat.Prime 509203 := by norm_num

lemma base_odd (m : ℕ) (hodd : Odd m) (h : 2 * m - m.totient = T) : False := by
  have hT : T = 2 * 509203 := rfl
  have hm1 : 1 < m := by
    rcases m with _ | _ | m
    · simp at hodd
    · simp [hT] at h
    · omega
  have hlt : m.totient < m := Nat.totient_lt m hm1
  have hmT : m < T := by omega
  -- m is squarefree
  have hsq : Squarefree m := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    have h1 : p ∣ m := dvd_trans (Dvd.intro p rfl) hpp
    have h2 : p ∣ m.totient := by
      have h3 : p ∣ (p * p).totient := by
        rw [← pow_two, Nat.totient_prime_pow hp (by norm_num)]
        simp
      exact dvd_trans h3 (Nat.totient_dvd_of_dvd hpp)
    have h4 : p ∣ 2 * 509203 := by
      have := Nat.dvd_sub (dvd_mul_of_dvd_right h1 2) h2
      rwa [h, hT] at this
    rcases (Nat.Prime.dvd_mul hp).1 h4 with h6 | h6
    · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h6
      subst this
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)
    · have : p = 509203 := (Nat.prime_dvd_prime_iff_eq hp M_prime).1 h6
      subst this
      have := Nat.le_of_dvd (by omega) hpp
      omega
  -- largest prime factor
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 hm1
  set q := m.primeFactors.max' hne with hqdef
  have hqmem : q ∈ m.primeFactors := Finset.max'_mem _ _
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hqmem
  set r := m / q with hrdef
  have hmr : m = q * r := (Nat.mul_div_cancel' hqm).symm
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmr
    omega
  have hrsq : Squarefree r := hsq.squarefree_of_dvd (Dvd.intro_left q hmr.symm)
  have hqr : ¬ q ∣ r := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    have : q * q ∣ m := ⟨c, by rw [hmr, hc]; ring⟩
    have hu := hsq q this
    exact hq.one_lt.ne' (Nat.isUnit_iff.1 hu)
  have hcop : Nat.Coprime q r := (Nat.Prime.coprime_iff_not_dvd hq).2 hqr
  have htot : m.totient = (q - 1) * r.totient := by
    rw [hmr, Nat.totient_mul hcop, Nat.totient_prime hq]
  have hrodd : Odd r := (Nat.odd_mul.1 (hmr ▸ hodd)).2
  -- prime factors of r are smaller than q
  have hlt_q : ∀ s ∈ r.primeFactors, s < q := by
    intro s hs
    have hsm : s ∈ m.primeFactors := by
      rw [Nat.mem_primeFactors] at hs ⊢
      exact ⟨hs.1, dvd_trans hs.2.1 (Dvd.intro_left q hmr.symm), by omega⟩
    have hle : s ≤ q := Finset.le_max' _ _ hsm
    have hne' : s ≠ q := by
      intro hsq'
      rw [hsq'] at hs
      exact hqr (Nat.dvd_of_mem_primeFactors hs)
    omega
  have hphr : r.totient ≤ r := Nat.totient_le r
  -- the equation in the search form
  have heq : q * (2 * r - r.totient) + r.totient = T := by
    rw [htot, hmr] at h
    obtain ⟨b, hb⟩ : ∃ b, r = r.totient + b := ⟨r - r.totient, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, q = c + 1 := ⟨q - 1, by have := hq.one_lt; omega⟩
    have e1 : 2 * r - r.totient = r.totient + 2 * b := by omega
    rw [e1]
    generalize r.totient = a at h hb e1 ⊢
    rw [hb, hc] at h
    rw [hc]
    simp only [Nat.add_sub_cancel] at h
    have e2 : 2 * ((c + 1) * (a + b)) = c * a + ((c + 1) * (a + 2 * b) + a) := by ring
    rw [e2] at h
    omega
  by_cases hr1 : r = 1
  · rw [hr1, Nat.totient_one] at heq
    have hq' : q = 1018405 := by rw [hT] at heq; omega
    rw [hq'] at hq
    norm_num at hq
  -- the list of prime factors of r
  set S := oddPrimes.filter (fun s => decide (s ∣ r)) with hS
  have hnd : oddPrimes.Nodup := oddPrimes_sorted.imp (fun h => ne_of_lt h)
  have hSnd : S.Nodup := hnd.filter _
  have hSfin : S.toFinset = r.primeFactors := by
    ext s
    simp only [List.mem_toFinset, hS, List.mem_filter, decide_eq_true_eq, Nat.mem_primeFactors]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨oddPrimes_prime s h1, h2, hr0⟩
    · rintro ⟨h1, h2, _⟩
      refine ⟨mem_oddPrimes s h1 ?_ ?_, h2⟩
      · rintro rfl
        exact (Nat.not_even_iff_odd.2 hrodd) (even_iff_two_dvd.2 h2)
      · have hs' : s < q := hlt_q s (Nat.mem_primeFactors.2 ⟨h1, h2, hr0⟩)
        have hsr : s ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) h2
        have : s * s < T := by
          calc s * s ≤ r * s := Nat.mul_le_mul_right s hsr
            _ < r * q := Nat.mul_lt_mul_of_pos_left hs' (Nat.pos_of_ne_zero hr0)
            _ = m := by rw [hmr]; ring
            _ < T := hmT
        rw [hT] at this
        nlinarith
  have hSprod : S.prod = r := by
    have := List.prod_toFinset (fun s => s) hSnd
    rw [hSfin, Nat.prod_primeFactors_of_squarefree hrsq] at this
    rw [this, List.map_id']
  have hSphi : (S.map (fun s => s - 1)).prod = r.totient := by
    rw [← List.prod_toFinset (fun s => s - 1) hSnd, hSfin, totient_sqf r hrsq]
  have hSne : S ≠ [] := by
    intro h0
    have : S.toFinset = ∅ := by rw [h0]; rfl
    rw [hSfin] at this
    have hne2 : r.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
    rw [this] at hne2
    exact Finset.not_nonempty_empty hne2
  refine sub_sound oddPrimes 1 1 sub_check oddPrimes_sorted
    (fun s hs => (oddPrimes_prime s hs).one_lt.le) (by norm_num) le_rfl S
    (List.filter_sublist) hSne q hq ?_ ?_ ?_
  · intro s hs
    apply hlt_q
    rw [← hSfin]
    exact List.mem_toFinset.2 hs
  · rw [hSprod, one_mul, mul_comm, ← hmr]
    exact hmT
  · rw [hSprod, hSphi, one_mul, one_mul]
    exact heq

lemma even_of (n X : ℕ) (h : n - n.totient = 2 * X) (hX : 0 < X) :
    ∃ m, n = 2 * m ∧ 2 ≤ m := by
  have hn3 : 3 ≤ n := by
    by_contra hc
    push Not at hc
    interval_cases n <;> simp at h <;> omega
  obtain ⟨a, ha⟩ := Nat.totient_even (by omega : 2 < n)
  have hle := Nat.totient_le n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨b, hb⟩
  · exact ⟨m, by omega, by omega⟩
  · omega

lemma tot_double_even (m : ℕ) (hm : Even m) : (2 * m).totient = 2 * m.totient :=
  Nat.totient_mul_of_prime_of_dvd Nat.prime_two (even_iff_two_dvd.1 hm)

lemma tot_double_odd (m : ℕ) (hm : Odd m) : (2 * m).totient = m.totient := by
  rw [Nat.totient_mul (Nat.coprime_two_left.2 hm), Nat.totient_two, one_mul]

lemma base (n : ℕ) (h : n - n.totient = 2 ^ (0 + 1) * 509203) : False := by
  have hT : T = 2 * 509203 := rfl
  have h' : n - n.totient = 2 * 509203 := by simpa using h
  obtain ⟨m, rfl, hm2⟩ := even_of n 509203 h' (by norm_num)
  rcases Nat.even_or_odd m with hme | hmo
  · rw [tot_double_even m hme] at h'
    by_cases hm : m = 2
    · subst hm
      norm_num at h'
    · obtain ⟨c, hc⟩ := hme
      obtain ⟨a, ha⟩ := Nat.totient_even (by omega : 2 < m)
      have := Nat.totient_le m
      omega
  · rw [tot_double_odd m hmo] at h'
    exact base_odd m hmo (by rw [hT]; exact h')

def covL : List ℕ := [3, 5, 7, 13, 17, 241]

def covB : Bool :=
  (List.range 24).all (fun i => covL.any (fun q => (2 ^ i * 509203) % q == 1)) &&
    covL.all (fun q => 2 ^ 24 % q == 1)

lemma covB_true : covB = true := by decide +kernel

lemma covL_bounds (q : ℕ) (hq : q ∈ covL) : 3 ≤ q ∧ q ≤ 241 := by
  simp only [covL, List.mem_cons, List.not_mem_nil, or_false] at hq
  omega

lemma cover (j : ℕ) : ∃ q ∈ covL, (2 ^ j * 509203) % q = 1 := by
  have h := covB_true
  unfold covB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨q, hq, hq1⟩ := h1 (j % 24) (Nat.mod_lt _ (by norm_num))
  refine ⟨q, hq, ?_⟩
  have hq24 := h2 q hq
  have hqb := covL_bounds q hq
  have e : 2 ^ j * 509203 = (2 ^ 24) ^ (j / 24) * (2 ^ (j % 24) * 509203) := by
    conv_lhs => rw [← Nat.div_add_mod j 24]
    rw [pow_add, pow_mul]
    ring
  rw [e, Nat.mul_mod, Nat.pow_mod, hq24, one_pow, hq1, Nat.one_mod_eq_one.2 (by omega), one_mul,
    Nat.one_mod_eq_one.2 (by omega)]

lemma step (k : ℕ) (IH : ∀ n, n - n.totient = 2 ^ (k + 1) * 509203 → False) (n : ℕ)
    (h : n - n.totient = 2 ^ (k + 1 + 1) * 509203) : False := by
  set X := 2 ^ k * 509203 with hX
  have hXpos : 0 < X := by positivity
  have hX2 : 509203 ≤ X := by
    rw [hX]
    have := Nat.one_le_two_pow (n := k)
    nlinarith
  have e2 : 2 ^ (k + 1 + 1) * 509203 = 2 * (2 * X) := by rw [hX]; ring
  have e1 : 2 ^ (k + 1) * 509203 = 2 * X := by rw [hX]; ring
  rw [e2] at h
  rw [e1] at IH
  obtain ⟨m, rfl, hm2⟩ := even_of n (2 * X) h (by omega)
  rcases Nat.even_or_odd m with hme | hmo
  · rw [tot_double_even m hme] at h
    exact IH m (by have := Nat.totient_le m; omega)
  · rw [tot_double_odd m hmo] at h
    have hm3 : 3 ≤ m := by obtain ⟨c, hc⟩ := hmo; omega
    have hlem := Nat.totient_le m
    -- φ(m) is not divisible by 4
    have h4 : ¬ 4 ∣ m.totient := by
      intro ⟨c, hc⟩
      obtain ⟨d, hd⟩ := hmo
      omega
    -- m is a prime power
    set p := m.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpodd : p ≠ 2 := by
      intro h2
      have := Nat.minFac_dvd m
      rw [← hp, h2] at this
      exact (Nat.not_even_iff_odd.2 hmo) (even_iff_two_dvd.2 this)
    obtain ⟨a, t, ht, hmt⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hpp.one_lt.ne'
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmt
      omega
    have ha : a ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hmt
      exact ht (hmt ▸ Nat.minFac_dvd m)
    have hcop : Nat.Coprime (p ^ a) t :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hpp).2 ht)
    have hpa_even : 2 ∣ (p ^ a).totient := by
      rw [Nat.totient_prime_pow hpp (Nat.pos_of_ne_zero ha)]
      apply dvd_mul_of_dvd_right
      rcases hpp.eq_two_or_odd with h2 | h2
      · exact absurd h2 hpodd
      · exact Nat.dvd_of_mod_eq_zero (by omega)
    have ht1 : t = 1 := by
      by_contra ht1
      have htodd : Odd t := (Nat.odd_mul.1 (hmt ▸ hmo)).2
      have ht3 : 2 < t := by obtain ⟨c, hc⟩ := htodd; omega
      have hte : 2 ∣ t.totient := even_iff_two_dvd.1 (Nat.totient_even ht3)
      apply h4
      rw [hmt, Nat.totient_mul hcop]
      obtain ⟨u, hu⟩ := hpa_even
      obtain ⟨v, hv⟩ := hte
      exact ⟨u * v, by rw [hu, hv]; ring⟩
    rw [ht1, mul_one] at hmt
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [hmt, Nat.totient_prime_pow hpp (by omega), Nat.add_sub_cancel] at h
    have hp1 : 1 ≤ p := hpp.one_lt.le
    have key : p ^ b * (p + 1) = 2 * (2 * X) := by
      obtain ⟨c, hc⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
      rw [hc] at h ⊢
      simp only [Nat.add_sub_cancel] at h
      have e3 : 2 * (c + 1) ^ (b + 1) = (c + 1) ^ b * c + (c + 1) ^ b * (c + 1 + 1) := by ring
      rw [e3] at h
      generalize (c + 1) ^ b * c = A at h
      omega
    rcases b with _ | b
    · -- p + 1 = 2 ^ (k+2) * M, but 2 ^ (k+2) * M - 1 has a small prime factor
      simp only [pow_zero, one_mul] at key
      obtain ⟨q, hq, hq1⟩ := cover (k + 1 + 1)
      rw [e2, ← key] at hq1
      have hqb := covL_bounds q hq
      have hqp : q ∣ p := by
        apply Nat.dvd_of_mod_eq_zero
        have h5 := Nat.mod_add_div p q
        have h6 := Nat.mod_lt p (by omega : 0 < q)
        rcases Nat.lt_or_ge (p % q) (q - 1) with h7 | h7
        · have : (p + 1) % q = p % q + 1 := by
            rw [Nat.add_mod, Nat.one_mod_eq_one.2 (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          omega
        · have h8 : p % q = q - 1 := by omega
          have : (p + 1) % q = 0 := by
            rw [Nat.add_mod, h8, Nat.one_mod_eq_one.2 (by omega), Nat.sub_add_cancel (by omega),
              Nat.mod_self]
          omega
      rcases hpp.eq_one_or_self_of_dvd q hqp with h8 | h8
      · omega
      · omega
    · -- p ∣ 2 ^ (k+2) * M forces p = M
      have hpd : p ∣ 2 ^ (k + 1 + 1) * 509203 := by
        rw [e2, ← key, pow_succ]
        exact Dvd.intro (p ^ b * (p + 1)) (by ring)
      rcases (Nat.Prime.dvd_mul hpp).1 hpd with h9 | h9
      · exact hpodd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h9))
      · have hpM : p = 509203 := (Nat.prime_dvd_prime_iff_eq hpp M_prime).1 h9
        rw [hpM] at key
        have key2 : 509203 ^ b * 509204 = 2 ^ (k + 1 + 1) := by
          have h10 : 509203 * (509203 ^ b * 509204) = 509203 * 2 ^ (k + 1 + 1) := by
            calc 509203 * (509203 ^ b * 509204) = 509203 ^ (b + 1) * (509203 + 1) := by ring
              _ = 2 * (2 * X) := key
              _ = 509203 * 2 ^ (k + 1 + 1) := by rw [hX]; ring
          exact Nat.eq_of_mul_eq_mul_left (by norm_num) h10
        have hP : Nat.Prime 127301 := by norm_num
        have h11 : 127301 ∣ 2 ^ (k + 1 + 1) := by
          rw [← key2]
          exact Dvd.intro (509203 ^ b * 4) (by ring)
        have := (Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).1 (hP.dvd_of_dvd_pow h11)
        norm_num at this

lemma main (k : ℕ) : ∀ n, n - n.totient = 2 ^ (k + 1) * 509203 → False := by
  induction k with
  | zero => exact base
  | succ k ih => exact step k ih

end OMA.O13b

theorem OMA.solution : type_of% @Erdos418.erdos_418.variants.soln := by
  rintro x ⟨k, rfl⟩ hmem
  obtain ⟨n, hn⟩ := hmem
  exact OMA.O13b.main k n hn
