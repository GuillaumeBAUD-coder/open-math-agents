import OMAStatements.S_oeis_a113573

namespace OMA.OeisA113573

open OMA.S_oeis_a113573

/-!
Every position `r ≥ 2` admits a pair of consecutive valid digits (`{2, 3}` when `r` is prime,
`{8, 9}` when `r` is composite) and also admits both an even and an odd valid digit (`{2, 3}`
when `r` is prime, `{8, 9}` when `r` is composite!).
Remarkably, the SAME pair `{2, 3}` (for prime `r`) and `{8, 9}` (for composite `r`) works for
BOTH 2-adic lifting AND mod-`u` sumset coverage!
-/

def baseDigit (r : ℕ) : ℕ :=
  if r = 1 then 1 else if r.Prime then 2 else 8

lemma baseDigit_lt_nine (r : ℕ) : baseDigit r < 9 := by
  unfold baseDigit
  split_ifs <;> omega

lemma baseDigit_valid (r : ℕ) (hr : 1 ≤ r) (b : Bool) (hb1 : r = 1 → b = false) :
    let d := baseDigit r + if b then 1 else 0
    d < 10 ∧ (r = 1 → d = 1) ∧ (r.Prime → d.Prime) ∧
      (2 ≤ r → ¬ r.Prime → 1 < d ∧ ¬ d.Prime) := by
  dsimp only
  unfold baseDigit
  by_cases h1 : r = 1
  · subst h1
    have hb : b = false := hb1 rfl
    subst hb
    refine ⟨by norm_num, fun _ => rfl, fun hp => absurd hp (by decide), fun h2 => by omega⟩
  · by_cases hp : r.Prime
    · rw [if_neg h1, if_pos hp]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;>
        exact ⟨by norm_num, fun h => absurd h h1, fun _ => by decide, fun _ hnp => absurd hp hnp⟩
    · rw [if_neg h1, if_neg hp]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;>
        exact ⟨by norm_num, fun h => absurd h h1, fun hp' => absurd hp' hp,
          fun _ _ => ⟨by norm_num, by decide⟩⟩

/-- Value of an `n`-digit decimal number from big-endian digit function `d : Fin n → ℕ`. -/
def evalDigits {n : ℕ} (d : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, d i * 10 ^ (n - 1 - i.val)

lemma ofDigits_reverse_eq_evalDigits {n : ℕ} (d : Fin n → ℕ) :
    Nat.ofDigits 10 (List.ofFn d).reverse = evalDigits d := by
  induction n with
  | zero => simp [evalDigits, Nat.ofDigits]
  | succ k ih =>
    have hrev : (List.ofFn d).reverse =
        d (Fin.last k) :: (List.ofFn (fun i : Fin k => d i.castSucc)).reverse := by
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
    rw [hrev, Nat.ofDigits_cons, ih (fun i : Fin k => d i.castSucc)]
    unfold evalDigits
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one,
      Fin.val_castSucc]
    rw [Finset.mul_sum]
    have hsum :
        ∑ i : Fin k, 10 * (d i.castSucc * 10 ^ (k - 1 - i.val)) =
          ∑ i : Fin k, d i.castSucc * 10 ^ (k - i.val) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : k - i.val = (k - 1 - i.val) + 1 := by omega
      rw [hi, pow_succ]
      ring
    rw [hsum, add_comm]

lemma digits_evalDigits {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hlt : ∀ i, d i < 10) (hlead : d ⟨0, by omega⟩ ≠ 0) :
    (Nat.digits 10 (evalDigits d)).reverse = List.ofFn d := by
  let L : List ℕ := (List.ofFn d).reverse
  have hof : Nat.ofDigits 10 L = evalDigits d := ofDigits_reverse_eq_evalDigits d
  have hltL : ∀ x ∈ L, x < 10 := by
    intro x hx
    rw [List.mem_reverse, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hlt i
  have hlast : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
    intro hne
    have h1 : L.getLast hne = (List.ofFn d).head (by intro h; apply hne; simp [L, h]) := by
      simp [L, List.getLast_reverse]
    rw [h1]
    have h2 : (List.ofFn d).head (by simp; omega) = d ⟨0, by omega⟩ := by
      cases n with
      | zero => omega
      | succ k => simp [List.ofFn_succ]
    rw [h2]
    exact hlead
  have hdig : Nat.digits 10 (evalDigits d) = L := by
    rw [← hof]
    exact Nat.digits_ofDigits 10 (by norm_num) L hltL hlast
  rw [hdig]
  exact List.reverse_reverse _

lemma goodDigits_of_bits {n : ℕ} (hn : 1 ≤ n) (b : Fin n → Bool)
    (hb0 : b ⟨0, by omega⟩ = false) :
    GoodDigits n (evalDigits (fun i => baseDigit (i.val + 1) + if b i then 1 else 0)) := by
  let d : Fin n → ℕ := fun i => baseDigit (i.val + 1) + if b i then 1 else 0
  have hlt : ∀ i, d i < 10 := fun i => by
    have := baseDigit_lt_nine (i.val + 1)
    cases h : b i <;> simp only [d, h, Bool.false_eq_true, ↓reduceIte, add_zero] <;> omega
  have hlead : d ⟨0, by omega⟩ ≠ 0 := by
    simp [d, baseDigit, hb0]
  have hrev := digits_evalDigits hn d hlt hlead
  refine ⟨?_, ?_⟩
  · have hlen := congrArg List.length hrev
    simpa [List.length_reverse, List.length_ofFn] using hlen
  · intro r hr1 hrn
    rw [hrev]
    have hidx : r - 1 < n := by omega
    have hget : (List.ofFn d).getD (r - 1) 0 = d ⟨r - 1, hidx⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hidx]
      rfl
    rw [hget]
    have hr_eq : (⟨r - 1, hidx⟩ : Fin n).val + 1 = r := by dsimp; omega
    have hvalid := baseDigit_valid r hr1 (b ⟨r - 1, hidx⟩) (fun hr1' => by
      have : (⟨r - 1, hidx⟩ : Fin n) = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [this]; exact hb0)
    simpa [d, hr_eq] using hvalid.2

/-- Elementary 2-adic lifting: given any choice of the top `n - a` digits, we can choose the
bottom `a` bits (`a ≤ n - 1`) so that `2^a ∣ evalDigits`. -/
lemma lift_two_pow {n : ℕ} (hn : 1 ≤ n) (a : ℕ) (ha : a ≤ n - 1) :
    ∃ tail : Fin a → Bool,
      ∀ head : Fin (n - a) → Bool,
        let b : Fin n → Bool := fun i =>
          if h : i.val < n - a then head ⟨i.val, h⟩ else tail ⟨i.val - (n - a), by omega⟩
        2 ^ a ∣ evalDigits (fun i => baseDigit (i.val + 1) + if b i then 1 else 0) := by
  induction a with
  | zero =>
    refine ⟨Fin.elim0, fun head => by simp⟩
  | succ k ih =>
    -- Prove directly by lifting the suffix sum `S_k = ∑_{j < k} d(n - 1 - j) * 10^j`!
    have hlift_suffix : ∀ (m : ℕ), m ≤ n - 1 →
        ∃ bits : Fin m → Bool,
          2 ^ m ∣ ∑ j : Fin m,
            (baseDigit (n - j.val) + if bits j then 1 else 0) * 10 ^ j.val := by
      intro m
      induction m with
      | zero => intro _; exact ⟨Fin.elim0, by simp⟩
      | succ t iht =>
        intro ht
        obtain ⟨bits, hdvd⟩ := iht (by omega)
        obtain ⟨q, hq⟩ := hdvd
        set base := baseDigit (n - t)
        let bit_t : Bool := decide (Odd (q + base * 5 ^ t))
        let bits' : Fin (t + 1) → Bool := Fin.snoc bits bit_t
        refine ⟨bits', ?_⟩
        rw [Fin.sum_univ_castSucc]
        have hcast : ∀ j : Fin t, bits' j.castSucc = bits j := fun j => by
          simp [bits', Fin.snoc_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, hcast, bits', Fin.snoc_last]
        rw [hq]
        have h10 : 10 ^ t = 2 ^ t * 5 ^ t := by rw [← mul_pow]; norm_num
        rw [h10]
        have hfac : 2 ^ t * q + (base + if bit_t then 1 else 0) * (2 ^ t * 5 ^ t) =
            2 ^ t * (q + (base + if bit_t then 1 else 0) * 5 ^ t) := by ring
        rw [hfac, pow_succ]
        refine Nat.mul_dvd_mul_left (2 ^ t) ?_
        have h5odd : Odd (5 ^ t) := Odd.pow (by decide)
        by_cases hodd : Odd (q + base * 5 ^ t)
        · have hb : bit_t = true := decide_eq_true hodd
          rw [hb, if_pos rfl]
          have : q + (base + 1) * 5 ^ t = (q + base * 5 ^ t) + 5 ^ t := by ring
          rw [this]
          exact even_iff_two_dvd.mp (hodd.add_odd h5odd)
        · have hb : bit_t = false := decide_eq_false hodd
          rw [hb, if_neg Bool.false_ne_true, add_zero]
          exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨bits, hbits_dvd⟩ := hlift_suffix (k + 1) ha
    let tail : Fin (k + 1) → Bool := fun j => bits ⟨k - j.val, by omega⟩
    refine ⟨tail, fun head => ?_⟩
    dsimp only
    let b : Fin n → Bool := fun i =>
      if h : i.val < n - (k + 1) then head ⟨i.val, h⟩ else tail ⟨i.val - (n - (k + 1)), by omega⟩
    let f : Fin n → ℕ := fun i =>
      (baseDigit (i.val + 1) + if b i then 1 else 0) * 10 ^ (n - 1 - i.val)
    change 2 ^ (k + 1) ∣ ∑ i : Fin n, f i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < n - (k + 1))]
    refine Nat.dvd_add ?_ ?_
    · refine Finset.dvd_sum fun i hi => ?_
      have hlt : i.val < n - (k + 1) := (Finset.mem_filter.mp hi).2
      have hexp : k + 1 ≤ n - 1 - i.val := by omega
      have hdvd1 : 2 ^ (k + 1) ∣ 10 ^ (k + 1) := by
        rw [show (10 : ℕ) ^ (k + 1) = 2 ^ (k + 1) * 5 ^ (k + 1) by rw [← mul_pow]; norm_num]
        exact dvd_mul_right _ _
      have hdvd2 : 10 ^ (k + 1) ∣ 10 ^ (n - 1 - i.val) := Nat.pow_dvd_pow 10 hexp
      exact dvd_mul_of_dvd_right (dvd_trans hdvd1 hdvd2) _
    · have hbij :
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < n - (k + 1)), f i =
            ∑ j : Fin (k + 1), (baseDigit (n - j.val) + if bits j then 1 else 0) * 10 ^ j.val := by
        refine Finset.sum_bij (fun i _ => ⟨n - 1 - i.val, by
          have := (Finset.mem_filter.mp ‹_›).2; omega⟩) ?_ ?_ ?_ ?_
        · intro i _; exact Finset.mem_univ _
        · intro i₁ hi₁ i₂ hi₂ heq
          have h1 := (Finset.mem_filter.mp hi₁).2
          have h2 := (Finset.mem_filter.mp hi₂).2
          have hv := congrArg Fin.val heq
          dsimp at hv
          exact Fin.ext (by omega)
        · intro j _
          refine ⟨⟨n - 1 - j.val, by omega⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          · exact Fin.ext (by dsimp; omega)
        · intro i hi
          have hge : ¬ i.val < n - (k + 1) := (Finset.mem_filter.mp hi).2
          have h1 : i.val + 1 = n - (n - 1 - i.val) := by omega
          have h2 : b i = bits ⟨n - 1 - i.val, by omega⟩ := by
            simp only [b, dif_neg hge, tail]
            congr 1; exact Fin.ext (by dsimp; omega)
          simp only [f, h1, h2]
      rw [hbij]
      exact hbits_dvd

/-- Adding a unit step `{0, c}` to a proper nonempty subset of `ZMod u` strictly increases size. -/
lemma card_union_add_unit_gt {u : ℕ} [NeZero u] (S : Finset (ZMod u))
    (hne : S.Nonempty) (hproper : S.card < u) {c : ZMod u} (hunit : IsUnit c) :
    S.card < (S ∪ S.image (· + c)).card := by
  classical
  by_contra hle
  have hsub : S ⊆ S ∪ S.image (· + c) := Finset.subset_union_left
  have heq : S ∪ S.image (· + c) = S :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hclosed : ∀ x ∈ S, x + c ∈ S := by
    intro x hx
    have hmem : x + c ∈ S ∪ S.image (· + c) := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)
    rwa [heq] at hmem
  have hclosed_mul : ∀ k : ℕ, ∀ x ∈ S, x + (k : ZMod u) * c ∈ S := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      have h1 := hclosed (x + (m : ZMod u) * c) (ih x hx)
      have h2 : x + ((m + 1 : ℕ) : ZMod u) * c = x + (m : ZMod u) * c + c := by
        push_cast; ring
      rwa [h2]
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨u_inv, hu_inv⟩ := hunit
  have huniv : S = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    set z : ZMod u := (y - x0) * (↑u_inv⁻¹ : ZMod u)
    have hnat : ((z.val : ℕ) : ZMod u) = z := ZMod.natCast_zmod_val z
    have hmem := hclosed_mul z.val x0 hx0
    have hy : x0 + (z.val : ZMod u) * c = y := by
      rw [hnat]
      dsimp only [z]
      rw [mul_assoc, ← hu_inv, Units.inv_mul, mul_one, add_sub_cancel]
    rwa [hy] at hmem
  rw [huniv, Finset.card_univ, ZMod.card] at hproper
  exact lt_irrefl _ hproper

/-- Any `L ≥ u - 1` unit weights in `ZMod u` cover all residues by `{0, 1}`-combinations. -/
lemma subset_sum_covers_zmod {u : ℕ} [NeZero u] :
    ∀ (L : ℕ) (w : Fin L → ZMod u), (∀ j, IsUnit (w j)) → u - 1 ≤ L →
      ∀ target : ZMod u, ∃ bits : Fin L → Bool,
        (∑ j : Fin L, if bits j then w j else 0) = target := by
  classical
  have hcard : ∀ (L : ℕ) (w : Fin L → ZMod u), (∀ j, IsUnit (w j)) →
      min u (L + 1) ≤ (Finset.univ.image (fun bits : Fin L → Bool =>
        ∑ j : Fin L, if bits j then w j else 0)).card := by
    intro L
    induction L with
    | zero =>
      intro w _
      have h1 : (Finset.univ.image (fun bits : Fin 0 → Bool =>
          ∑ j : Fin 0, if bits j then w j else 0)).card = 1 := by
        have heq : Finset.univ.image (fun bits : Fin 0 → Bool =>
            ∑ j : Fin 0, if bits j then w j else 0) = {(0 : ZMod u)} := by
          ext x
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton,
            Finset.univ_eq_empty, Finset.sum_empty]
          exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨Fin.elim0, h.symm⟩⟩
        rw [heq, Finset.card_singleton]
      rw [h1]
      exact min_le_right u 1
    | succ k ih =>
      intro w hw
      let w' : Fin k → ZMod u := fun j => w j.castSucc
      set S := Finset.univ.image (fun bits : Fin k → Bool =>
        ∑ j : Fin k, if bits j then w' j else 0)
      set S' := Finset.univ.image (fun bits : Fin (k + 1) → Bool =>
        ∑ j : Fin (k + 1), if bits j then w j else 0)
      have hS'_eq : S' = S ∪ S.image (· + w (Fin.last k)) := by
        ext x
        simp only [S', S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨bits, rfl⟩
          rw [Fin.sum_univ_castSucc]
          cases hb : bits (Fin.last k)
          · left
            refine ⟨fun j => bits j.castSucc, ?_⟩
            simp [w']
          · right
            refine ⟨∑ j : Fin k, if bits j.castSucc then w' j else 0,
              ⟨fun j => bits j.castSucc, rfl⟩, ?_⟩
            simp [w']
        · rintro (⟨bits, rfl⟩ | ⟨y, ⟨bits, rfl⟩, rfl⟩)
          · refine ⟨Fin.snoc bits false, ?_⟩
            rw [Fin.sum_univ_castSucc]
            simp [w', Fin.snoc_castSucc, Fin.snoc_last]
          · refine ⟨Fin.snoc bits true, ?_⟩
            rw [Fin.sum_univ_castSucc]
            simp [w', Fin.snoc_castSucc, Fin.snoc_last]
      have hih : min u (k + 1) ≤ S.card := ih w' (fun j => hw j.castSucc)
      have hne : S.Nonempty := ⟨0, Finset.mem_image.mpr ⟨fun _ => false, Finset.mem_univ _, by simp⟩⟩
      rw [hS'_eq]
      by_cases hfull : S.card < u
      · have hgt := card_union_add_unit_gt S hne hfull (hw (Fin.last k))
        omega
      · have hle : S.card ≤ (S ∪ S.image (· + w (Fin.last k))).card :=
          Finset.card_le_card Finset.subset_union_left
        omega
  intro L w hw hL target
  set S := Finset.univ.image (fun bits : Fin L → Bool =>
    ∑ j : Fin L, if bits j then w j else 0)
  have hu_pos : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  have hge : u ≤ S.card := by
    have h1 : min u (L + 1) ≤ S.card := hcard L w hw
    omega
  have huniv : S = Finset.univ := Finset.eq_univ_of_card S (by
    rw [ZMod.card]; exact le_antisymm (by simpa [ZMod.card] using Finset.card_le_univ S) hge)
  have hmem : target ∈ S := huniv ▸ Finset.mem_univ target
  obtain ⟨bits, _, hsum⟩ := Finset.mem_image.mp hmem
  exact ⟨bits, hsum⟩

lemma two_pow_mul_ge_add (a u : ℕ) (hu : 1 ≤ u) : a + u ≤ 2 ^ a * u := by
  have hpow : a + 1 ≤ 2 ^ a := by
    induction a with
    | zero => simp
    | succ k ih =>
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
  nlinarith

lemma case_five : ∃ m, 5 ∣ m ∧ GoodDigits 5 m := by
  refine ⟨12245, ⟨2449, by norm_num⟩, ?_⟩
  have hdig : Nat.digits 10 12245 = [5, 4, 2, 2, 1] := by decide
  refine ⟨by rw [hdig]; rfl, ?_⟩
  intro r hr1 hr5
  rw [hdig]
  interval_cases r <;> decide

lemma case_not_five_dvd {n : ℕ} (hn : 1 ≤ n) (h5 : ¬ 5 ∣ n) :
    ∃ m, n ∣ m ∧ GoodDigits n m := by
  set a := n.factorization 2
  have h2a_dvd : 2 ^ a ∣ n := Nat.ordProj_dvd n 2
  set u := n / 2 ^ a
  have hmul : 2 ^ a * u = n := Nat.mul_div_cancel' h2a_dvd
  have hu_pos : 1 ≤ u :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega
  haveI : NeZero u := ⟨by omega⟩
  have hnot2u : ¬ 2 ∣ u := by
    intro h2u
    rcases h2u with ⟨r, hr⟩
    have hdvd : 2 ^ (a + 1) ∣ n := ⟨r, by rw [← hmul, hr]; ring⟩
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hdvd
    omega
  have hnot5u : ¬ 5 ∣ u := fun h5u => h5 (dvd_trans h5u ⟨2 ^ a, by rw [mul_comm, hmul]⟩)
  have hcop2u : Nat.Coprime (2 ^ a) u :=
    Nat.Coprime.pow_left a (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2u)
  have hcop10u : Nat.Coprime 10 u := by
    have h2 : Nat.Coprime 2 u := Nat.prime_two.coprime_iff_not_dvd.mpr hnot2u
    have h5' : Nat.Coprime 5 u := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hnot5u
    simpa using h2.mul_left h5'
  have ha_le : a + u ≤ n := by rw [← hmul]; exact two_pow_mul_ge_add a u hu_pos
  obtain ⟨tail, htail⟩ := lift_two_pow hn a (by omega)
  set L := n - a - 1
  have hL : u - 1 ≤ L := by omega
  let w : Fin L → ZMod u := fun j => ((10 : ZMod u) ^ (n - 1 - (j.val + 1)))
  have hunit10 : IsUnit (10 : ZMod u) := (ZMod.isUnit_iff_coprime 10 u).mpr hcop10u
  have hw_unit : ∀ j : Fin L, IsUnit (w j) := fun j => hunit10.pow _
  -- Base number when head bits are all false
  let b0 : Fin n → Bool := fun i =>
    if h : i.val < n - a then false else tail ⟨i.val - (n - a), by omega⟩
  let m0 : ℕ := evalDigits (fun i => baseDigit (i.val + 1) + if b0 i then 1 else 0)
  obtain ⟨mid, hmid⟩ := subset_sum_covers_zmod L w hw_unit hL (-(m0 : ZMod u))
  let head : Fin (n - a) → Bool := fun i =>
    if h : i.val = 0 then false else mid ⟨i.val - 1, by omega⟩
  let b : Fin n → Bool := fun i =>
    if h : i.val < n - a then head ⟨i.val, h⟩ else tail ⟨i.val - (n - a), by omega⟩
  let m : ℕ := evalDigits (fun i => baseDigit (i.val + 1) + if b i then 1 else 0)
  refine ⟨m, ?_, ?_⟩
  · rw [← hmul]
    refine hcop2u.mul_dvd_of_dvd_of_dvd (htail head) ?_
    rw [← ZMod.natCast_eq_zero_iff]
    have hm_eq : m = m0 + ∑ j : Fin L, (if mid j then 1 else 0) * 10 ^ (n - 1 - (j.val + 1)) := by
      unfold m m0 evalDigits
      have hterm : ∀ i : Fin n,
          (baseDigit (i.val + 1) + if b i then 1 else 0) * 10 ^ (n - 1 - i.val) =
            (baseDigit (i.val + 1) + if b0 i then 1 else 0) * 10 ^ (n - 1 - i.val) +
              (if h : 1 ≤ i.val ∧ i.val < n - a then
                (if mid ⟨i.val - 1, by omega⟩ then 1 else 0) * 10 ^ (n - 1 - i.val) else 0) := by
        intro i
        by_cases hlt : i.val < n - a
        · by_cases h0 : i.val = 0
          · simp [b, b0, head, hlt, h0]
          · have hcond : 1 ≤ i.val ∧ i.val < n - a := ⟨by omega, hlt⟩
            simp only [b, b0, head, dif_pos hlt, dif_neg h0, dif_pos hcond, Bool.false_eq_true,
              ↓reduceIte, add_zero]
            ring
        · have hnot : ¬ (1 ≤ i.val ∧ i.val < n - a) := fun h => hlt h.2
          simp [b, b0, hlt, hnot]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => 1 ≤ i.val ∧ i.val < n - a)]
      have hzero_rest :
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (1 ≤ i.val ∧ i.val < n - a)),
            (if h : 1 ≤ i.val ∧ i.val < n - a then
              (if mid ⟨i.val - 1, by omega⟩ then 1 else 0) * 10 ^ (n - 1 - i.val) else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [dif_neg (Finset.mem_filter.mp hi).2]
      rw [hzero_rest, add_zero]
      refine Finset.sum_bij (fun i hi => ⟨i.val - 1, by
        have := (Finset.mem_filter.mp hi).2; omega⟩) ?_ ?_ ?_ ?_
      · intro i _; exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ heq
        have h1 := (Finset.mem_filter.mp hi₁).2
        have h2 := (Finset.mem_filter.mp hi₂).2
        have hv := congrArg Fin.val heq
        dsimp at hv
        exact Fin.ext (by omega)
      · intro j _
        refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
        · exact Fin.ext (by simp)
      · intro i hi
        have h1 := (Finset.mem_filter.mp hi).2
        rw [dif_pos h1]
        have heq : i.val - 1 + 1 = i.val := by omega
        simp only [heq]
    rw [hm_eq, Nat.cast_add, Nat.cast_sum]
    have hsum_cast :
        (∑ j : Fin L, (((if mid j then 1 else 0) * 10 ^ (n - 1 - (j.val + 1)) : ℕ) : ZMod u)) =
          ∑ j : Fin L, if mid j then w j else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      cases mid j <;> simp [w]
    rw [hsum_cast, hmid, add_neg_cancel]
  · refine goodDigits_of_bits hn b ?_
    have h0 : (0 : ℕ) < n - a := by omega
    simp [b, head, h0]

end OMA.OeisA113573

theorem OMA.solution : type_of% @OMA.S_oeis_a113573.main := by
  intro n hn hnot5t
  by_cases h5 : 5 ∣ n
  · obtain ⟨t, rfl⟩ := h5
    have ht1 : t = 1 := by
      by_contra hne
      have ht_pos : 0 < t := by
        by_contra h0; have : t = 0 := by omega
        subst this; omega
      exact hnot5t ⟨t, by omega, rfl⟩
    subst ht1
    simpa using OMA.OeisA113573.case_five
  · exact OMA.OeisA113573.case_not_five_dvd hn h5
