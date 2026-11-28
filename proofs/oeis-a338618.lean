import OMAStatements.S_oeis_a338618

-- Credit: @RiverMint78

/-!
The least eligible unused value extends each finite prefix.
If a value m were omitted, it would forbid adjacent common factors in the tail.
The term two places later is then an eligible comparison at each choice, so that
tail increases. A sufficiently large composite term would make a smaller unused
multiple of m eligible, forcing a tail of distinct primes, which is impossible.
-/

namespace A338618Proof

open OMA.S_oeis_a338618

private def shares (x y : ℕ+) : Prop :=
  1 < Nat.gcd (x : ℕ) (y : ℕ)

private def good (x y z : ℕ+) : Prop :=
  shares x y ∨ shares x z ∨ shares y z

private theorem shares_of_dvd {x y : ℕ+} {d : ℕ} (hd : 1 < d)
    (hx : d ∣ (x : ℕ)) (hy : d ∣ (y : ℕ)) : shares x y :=
  hd.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ x.pos) (Nat.dvd_gcd hx hy))

private def total (l : List ℕ+) : ℕ := (l.map PNat.val).sum

private theorem le_total {l : List ℕ+} {x : ℕ+} (h : x ∈ l) : (x : ℕ) ≤ total l := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
      rcases List.mem_cons.mp h with he | hm
      · subst x
        change (y : ℕ) ≤ (y : ℕ) + total l
        omega
      · have hh := ih hm
        change (x : ℕ) ≤ (y : ℕ) + total l
        omega

private theorem fresh_mul (l : List ℕ+) (x : ℕ+) : (total l).succPNat * x ∉ l := by
  intro h
  have hs := le_total h
  change (total l + 1) * (x : ℕ) ≤ total l at hs
  have hh : total l + 1 ≤ (total l + 1) * (x : ℕ) := by
    simpa using Nat.mul_le_mul_left (total l + 1) x.pos
  omega

private def allowed (l : List ℕ+) (z : ℕ+) : Prop :=
  z ∉ l ∧
    match l with
    | y :: x :: _ => good x y z
    | _ => True

private theorem allowed_exists {l : List ℕ+} (hn : l.Nodup) : ∃ z, allowed l z := by
  rcases l with _ | ⟨y, tail⟩
  · exact ⟨1, by simp [allowed]⟩
  rcases tail with _ | ⟨x, tail⟩
  · let z := (total [y]).succPNat * y
    exact ⟨z, fresh_mul [y] y, trivial⟩
  let l := y :: x :: tail
  by_cases hx : 1 < (x : ℕ)
  · let z := (total l).succPNat * x
    have hd : (x : ℕ) ∣ (z : ℕ) := by
      change (x : ℕ) ∣ (total l + 1) * (x : ℕ)
      exact dvd_mul_left _ _
    exact ⟨z, fresh_mul l x, Or.inr (Or.inl (shares_of_dvd hx (dvd_refl _) hd))⟩
  · have hyx : y ≠ x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hy : 1 < (y : ℕ) := by
      have hxPos := x.pos
      have hyPos := y.pos
      by_contra! h
      exact hyx (Subtype.ext (by omega : (y : ℕ) = (x : ℕ)))
    let z := (total l).succPNat * y
    have hd : (y : ℕ) ∣ (z : ℕ) := by
      change (y : ℕ) ∣ (total l + 1) * (y : ℕ)
      exact dvd_mul_left _ _
    exact ⟨z, fresh_mul l y, Or.inr (Or.inr (shares_of_dvd hy (dvd_refl _) hd))⟩

private noncomputable def nextTerm (l : List ℕ+) : ℕ+ := by
  classical
  exact if h : l.Nodup then PNat.find (allowed_exists h) else 1

private theorem next_spec {l : List ℕ+} (h : l.Nodup) :
    allowed l (nextTerm l) ∧ ∀ x, allowed l x → nextTerm l ≤ x := by
  classical
  rw [nextTerm, dif_pos h]
  exact ⟨PNat.find_spec _, fun _ hx => PNat.find_min' _ hx⟩

private noncomputable def priorTerms : ℕ → List ℕ+
  | 0 => []
  | n + 1 => nextTerm (priorTerms n) :: priorTerms n

private noncomputable def seq (n : ℕ) : ℕ+ := nextTerm (priorTerms n)

private theorem prefix_nodup (n : ℕ) : (priorTerms n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
      exact List.nodup_cons.mpr ⟨(next_spec ih).1.1, ih⟩

private theorem mem_prefix {x : ℕ+} {n : ℕ} : x ∈ priorTerms n ↔ ∃ i < n, seq i = x := by
  induction n with
  | zero => simp [priorTerms]
  | succ n ih =>
      change x ∈ seq n :: priorTerms n ↔ _
      rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨n, by omega, rfl⟩
        · exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, he⟩
        rcases lt_or_eq_of_le (show i ≤ n by omega) with hh | rfl
        · exact Or.inr ⟨i, hh, he⟩
        · exact Or.inl he.symm

private theorem seq_ne_of_lt {i j : ℕ} (h : i < j) : seq i ≠ seq j := by
  intro he
  exact (next_spec (prefix_nodup j)).1.1 (mem_prefix.mpr ⟨i, h, he⟩)

private theorem seq_injective : Function.Injective seq := by
  intro i j h
  rcases lt_trichotomy i j with hl | he | hg
  · exact (seq_ne_of_lt hl h).elim
  · exact he
  · exact (seq_ne_of_lt hg h.symm).elim

private theorem seq_zero : seq 0 = 1 :=
  le_antisymm ((next_spec (prefix_nodup 0)).2 1 (by simp [priorTerms, allowed])) one_le

private theorem seq_good (n : ℕ) : good (seq n) (seq (n + 1)) (seq (n + 2)) :=
  (next_spec (prefix_nodup (n + 2))).1.2

private theorem seq_min (n : ℕ) (x : ℕ+) (fresh : ∀ i < n + 2, seq i ≠ x)
    (hx : good (seq n) (seq (n + 1)) x) : seq (n + 2) ≤ x := by
  apply (next_spec (prefix_nodup (n + 2))).2
  exact ⟨fun hm => let ⟨i, hi, h⟩ := mem_prefix.mp hm; fresh i hi h, hx⟩

private theorem escapes (B : ℕ) : ∃ N : ℕ, ∀ i, N ≤ i → B < (seq i : ℕ) := by
  have hInj : Function.Injective (fun i => (seq i : ℕ)) :=
    fun _ _ h => seq_injective (Subtype.ext h)
  have hFin : (fun i => (seq i : ℕ)) ⁻¹' Set.Iic B |>.Finite :=
    (Set.finite_Iic B).preimage hInj.injOn
  obtain ⟨u, hu⟩ := hFin.bddAbove
  refine ⟨u + 1, fun i hi => lt_of_not_ge fun h => ?_⟩
  have hle : i ≤ u := hu h
  omega

private theorem no_large_composite {v M : ℕ} (hv : 0 < v) (hM : M * M < v)
    (hComp : ¬v.Prime) (hOne : v ≠ 1) :
    ∃ q : ℕ, 1 < q ∧ q ∣ v ∧ M * q < v := by
  let q := v.minFac
  have hp : q.Prime := Nat.minFac_prime hOne
  have hs : q * q ≤ v := by simpa [pow_two, q] using Nat.minFac_sq_le_self hv hComp
  refine ⟨q, hp.one_lt, Nat.minFac_dvd _, ?_⟩
  rcases le_or_gt q M with h | h
  · exact (Nat.mul_le_mul_left M h).trans_lt hM
  · exact (Nat.mul_lt_mul_of_pos_right h hp.pos).trans_le hs

private theorem seq_surjective : Function.Surjective seq := by
  intro m
  by_contra hmiss
  have missing (i : ℕ) : seq i ≠ m := fun h => hmiss ⟨i, h⟩
  have hm : 1 < (m : ℕ) := by
    have h1 : m ≠ 1 := fun h => missing 0 (seq_zero.trans h.symm)
    exact show (1 : ℕ+) < m from lt_of_le_of_ne one_le h1.symm
  obtain ⟨N, hN⟩ := escapes (m : ℕ)
  have no_adjacent (i : ℕ) (hi : N ≤ i) : ¬shares (seq i) (seq (i + 1)) := by
    intro hs
    exact (not_le_of_gt (hN (i + 2) (by omega))) (seq_min i m (fun j _ => missing j) (Or.inl hs))
  have no_shared_m (i : ℕ) (hi : N ≤ i) : ¬shares (seq i) m := by
    intro hs
    exact (not_le_of_gt (hN (i + 2) (by omega)))
      (seq_min i m (fun j _ => missing j) (Or.inr (Or.inl hs)))
  have two_back (i : ℕ) (hi : N ≤ i) : shares (seq i) (seq (i + 2)) := by
    rcases seq_good i with h | h | h
    · exact (no_adjacent i hi h).elim
    · exact h
    · exact (no_adjacent (i + 1) (by omega) h).elim
  have grows (i : ℕ) (hi : N + 2 ≤ i) : seq i < seq (i + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    exact lt_of_le_of_ne (seq_min j (seq (j + 3)) (fun k hk => seq_ne_of_lt (by omega))
      (Or.inr (Or.inr (two_back (j + 1) (by omega))))) (seq_ne_of_lt (by omega))
  let B := total (priorTerms N) + 1
  let M := B * (m : ℕ)
  obtain ⟨I, hI⟩ := escapes (M * M + 1)
  let T := max (N + 2) I
  have late_prime (i : ℕ) (hi : T ≤ i) : (seq i : ℕ).Prime := by
    have hiN : N + 2 ≤ i := (le_max_left _ _).trans hi
    have hiI : I ≤ i := (le_max_right _ _).trans hi
    have hBig := hI i hiI
    by_contra hn
    obtain ⟨q, hq, hqDvd, hsmall⟩ :=
      no_large_composite (seq i).pos (show M * M < (seq i : ℕ) by omega) hn (by omega)
    have hMpos : 0 < M := Nat.mul_pos (by simp [B]) m.pos
    let w : ℕ+ := ⟨M * q, Nat.mul_pos hMpos (by omega)⟩
    have hd : (m : ℕ) ∣ (w : ℕ) := by
      refine ⟨B * q, ?_⟩
      change B * (m : ℕ) * q = (m : ℕ) * (B * q)
      ac_rfl
    have fresh (j : ℕ) : seq j ≠ w := by
      intro he
      by_cases hj : N ≤ j
      · exact no_shared_m j hj (shares_of_dvd hm (he ▸ hd) (dvd_refl _))
      · have hb := le_total (mem_prefix.mpr ⟨j, by omega, rfl⟩ : seq j ∈ priorTerms N)
        have hBw : B ≤ (w : ℕ) := by
          change B ≤ B * (m : ℕ) * q
          have hM : B ≤ B * (m : ℕ) := by simpa using Nat.mul_le_mul_left B m.pos
          have hq' : B * (m : ℕ) ≤ B * (m : ℕ) * q := by
            simpa using Nat.mul_le_mul_left (B * (m : ℕ)) (show 1 ≤ q by omega)
          exact hM.trans hq'
        have hw := congrArg PNat.val he
        dsimp [B] at hBw
        omega
    have hg : good (seq i) (seq (i + 1)) w :=
      Or.inr (Or.inl (shares_of_dvd hq hqDvd (dvd_mul_left _ _)))
    have hmin : seq (i + 2) ≤ w := seq_min i w (fun j _ => fresh j) hg
    exact (not_le_of_gt (show w < seq (i + 2) from
      (show w < seq i from hsmall).trans ((grows i hiN).trans (grows (i + 1) (by omega))))) hmin
  have hcop : Nat.Coprime (seq T : ℕ) (seq (T + 2) : ℕ) :=
    (Nat.coprime_primes (late_prime T le_rfl) (late_prime (T + 2) (by omega))).mpr
      (fun he => seq_ne_of_lt (by omega) (Subtype.ext he))
  have hs := two_back T (show N ≤ T from (by omega : N ≤ N + 2).trans (le_max_left _ _))
  exact (not_lt_of_ge (le_of_eq hcop)) hs

private theorem seq_min_matching (b : ℕ → ℕ+) (hb : Function.Injective b)
    (hg : ∀ i, good (b i) (b (i + 1)) (b (i + 2)))
    (n : ℕ) (hprev : ∀ j < n, seq j = b j) : seq n ≤ b n := by
  have fresh : (b n) ∉ priorTerms n := by
    intro hm
    obtain ⟨j, hj, he⟩ := mem_prefix.mp hm
    exact (ne_of_lt hj) (hb ((hprev j hj).symm.trans he))
  apply (next_spec (prefix_nodup n)).2
  refine ⟨fresh, ?_⟩
  rcases n with _ | _ | i
  · trivial
  · trivial
  · change good (seq i) (seq (i + 1)) (b (i + 2))
    rw [hprev i (by omega), hprev (i + 1) (by omega)]
    exact hg i

private theorem pred_plus_one (i : ℕ+) : (i + 1).natPred = i.natPred + 1 := by
  rw [PNat.add_one, Nat.natPred_succPNat, PNat.natPred_add_one]

private theorem succPNat_plus_one (i : ℕ) : i.succPNat + 1 = (i + 1).succPNat := rfl

private theorem lift_good (b : ℕ+ → ℕ+) (hb : Admissible b) (n : ℕ) :
    good (b n.succPNat) (b (n + 1).succPNat) (b (n + 2).succPNat) := by
  have hh := hb.2 n.succPNat
  change good (b n.succPNat) (b (n.succPNat + 1)) (b (n.succPNat + 2)) at hh
  rw [show n.succPNat + 2 = (n.succPNat + 1) + 1 by rfl,
    succPNat_plus_one, succPNat_plus_one] at hh
  exact hh

end A338618Proof

open A338618Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a338618.main := by
  let a : ℕ+ → ℕ+ := fun i => seq i.natPred
  refine ⟨a, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact seq_injective.comp PNat.natPred_injective
  · intro i
    change good (seq i.natPred) (seq (i + 1).natPred) (seq (i + 2).natPred)
    simp only [show i + 2 = (i + 1) + 1 by rfl, pred_plus_one]
    exact seq_good _
  · intro b hb
    by_cases h : a = b
    · rw [h]
    have hex := Function.ne_iff.mp h
    let i := PNat.find hex
    have hne : a i ≠ b i := PNat.find_spec hex
    have hp (j : ℕ+) (hj : j < i) : a j = b j := by
      by_contra hnj
      exact PNat.find_min hex hj hnj
    have hle : a i ≤ b i := by
      let c : ℕ → ℕ+ := fun n => b n.succPNat
      have hc := seq_min_matching c (hb.1.comp Nat.succPNat_injective) (lift_good b hb)
        i.natPred (fun j hj => by
          have hj' : j.succPNat < i := by
            rw [← PNat.natPred_lt_natPred, Nat.natPred_succPNat]
            exact hj
          simpa [a, c] using hp j.succPNat hj')
      simpa [a, c] using hc
    exact le_of_lt (show Pi.Lex (· < ·) (· < ·) a b from ⟨i, hp, lt_of_le_of_ne hle hne⟩)
  · intro x
    obtain ⟨i, hi⟩ := seq_surjective x
    exact ⟨i.succPNat, by simpa [a] using hi⟩
