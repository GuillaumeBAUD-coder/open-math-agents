import FormalConjectures.ErdosProblems.«455»

-- Problem: Erdős Problem 455, liminf variant (Richter 1976)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/455.lean:45 (declaration Erdos455.erdos_455.variants.liminf)

/-!
# Primes with nondecreasing gaps grow quadratically

Let `g i = q (i+1) - q i`. Since the gaps are nondecreasing, the indices with a given gap `d`
form a run, so the corresponding primes form an arithmetic progression with difference `d`.
For a prime `p` not dividing `d` with `p ≤ d + 1`, such a progression has at most `p` terms, so
each gap value occurs at most `p - 1` times. Taking `p` least gives at most
`#{m ≤ d : primorial m ∣ d}` occurrences; odd gaps occur at most once (they start at `2`), and a
gap `d` with `2 ∣ d`, `3 ∤ d` occurs at most once except for the run starting at `3`. Summing,
at most `3 + (23/20) D` gaps are `≤ D`, using `∑_{m ≥ 5} 1/primorial m ≤ 3/20` (from Bertrand).
Hence `g i ≥ (i - 2)/(23/20)` and `q n ≥ (9/25) n^2` for `n ≥ 100`.
-/
namespace E455

def g (q : ℕ → ℕ) (i : ℕ) : ℕ := q (i + 1) - q i

lemma q_succ {q : ℕ → ℕ} (hq : StrictMono q) (i : ℕ) : q (i + 1) = q i + g q i := by
  have := hq (show i < i + 1 by omega); unfold g; omega

lemma q_ap {q : ℕ → ℕ} (hq : StrictMono q) (i d : ℕ) :
    ∀ k, (∀ j < k, g q (i + j) = d) → q (i + k) = q i + k * d := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    rw [← add_assoc, q_succ hq, ih (fun j hj => h j (by omega)), h k (by omega)]
    ring

/-- the indices below `n` whose gap is `d` -/
def S (q : ℕ → ℕ) (n d : ℕ) : Finset ℕ := (Finset.range n).filter (fun i => g q i = d)

lemma run_long {q : ℕ → ℕ} (hg : Monotone (g q)) (n d k : ℕ) (hk : k ≤ (S q n d).card)
    (hne : (S q n d).Nonempty) :
    ∀ j < k, g q ((S q n d).min' hne + j) = d := by
  intro j hj
  set s := (S q n d).min' hne
  set t := (S q n d).max' hne
  have hs : s ∈ S q n d := Finset.min'_mem _ _
  have ht : t ∈ S q n d := Finset.max'_mem _ _
  have hsub : S q n d ⊆ Finset.Icc s t := fun x hx =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hcard
  have hgs : g q s = d := (Finset.mem_filter.mp hs).2
  have hgt : g q t = d := (Finset.mem_filter.mp ht).2
  apply le_antisymm
  · rw [← hgt]; exact hg (by omega)
  · rw [← hgs]; exact hg (by omega)

lemma run_bound {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (n d p : ℕ) (hd : 1 ≤ d) (pp : p.Prime) (hpd : ¬ p ∣ d) (hpd1 : p ≤ d + 1) :
    (S q n d).card ≤ p - 1 := by
  by_contra hc
  push Not at hc
  have hne : (S q n d).Nonempty := Finset.card_pos.mp (by omega)
  set s := (S q n d).min' hne
  have hrun := run_long hg n d p (by omega) hne
  have hap : ∀ k ≤ p, q (s + k) = q s + k * d := fun k hk =>
    q_ap hq s d k (fun j hj => hrun j (by omega))
  have := Fact.mk pp
  have hdz : (d : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set k0 := ((-(q s : ZMod p)) / (d : ZMod p)).val with hk0
  have hk0lt : k0 < p := ZMod.val_lt _
  have hdiv : p ∣ q s + k0 * d := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hk0, ZMod.natCast_zmod_val]
    field_simp
    ring
  have hqs2 := (hp s).two_le
  rcases Nat.eq_zero_or_pos k0 with h0 | h0
  · rw [h0] at hdiv; simp at hdiv
    have hqs : q s = p := ((Nat.prime_dvd_prime_iff_eq pp (hp s)).mp hdiv).symm
    have := hp (s + p)
    rw [hap p le_rfl, hqs, show p + p * d = p * (1 + d) by ring] at this
    rcases Nat.prime_mul_iff.mp this with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · exact pp.ne_one h
  · have hpr := hp (s + k0)
    rw [hap k0 hk0lt.le] at hpr
    have heq := (Nat.prime_dvd_prime_iff_eq pp hpr).mp hdiv
    have : d ≤ k0 * d := Nat.le_mul_of_pos_left d h0
    omega

open Classical in
lemma odd_bound {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (n d : ℕ) (hd : ¬ 2 ∣ d) :
    (S q n d).card ≤ if (∃ i, q i = 2 ∧ g q i = d) then 1 else 0 := by
  have hd1 : 1 ≤ d := by rcases Nat.eq_zero_or_pos d with h | h <;> [simp [h] at hd; omega]
  have hb := run_bound hq hp hg n d 2 hd1 Nat.prime_two hd (by omega)
  split_ifs with hex
  · omega
  · rcases Nat.eq_zero_or_pos (S q n d).card with h | h
    · omega
    · exfalso
      obtain ⟨i, hi⟩ := Finset.card_pos.mp h
      have hgi : g q i = d := (Finset.mem_filter.mp hi).2
      apply hex ⟨i, ?_, hgi⟩
      have h1 := q_succ hq i
      rcases (hp i).eq_two_or_odd' with h2 | h2
      · exact h2
      · rcases (hp (i + 1)).eq_two_or_odd' with h3 | h3
        · have := hq (show i < i + 1 by omega); have := (hp i).two_le; omega
        · exfalso; apply hd
          have : Odd (q i + g q i) := h1 ▸ h3
          rw [← hgi]
          rcases h2 with ⟨a, ha⟩; rcases this with ⟨b, hb⟩
          exact ⟨b - a, by omega⟩

open Classical in
lemma three_bound {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (n d : ℕ) (hd2 : 2 ∣ d) (hd3 : ¬ 3 ∣ d) :
    (S q n d).card ≤ 1 + if (∃ i, q i = 3 ∧ g q i = d) then 1 else 0 := by
  have hd1 : 2 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h] at hd3
    · exact Nat.le_of_dvd h hd2 |> fun _ => by obtain ⟨c, hc⟩ := hd2; omega
  have hb := run_bound hq hp hg n d 3 (by omega) Nat.prime_three hd3 (by omega)
  split_ifs with hex
  · omega
  · by_contra hc
    push Not at hc
    have hne : (S q n d).Nonempty := Finset.card_pos.mp (by omega)
    set s := (S q n d).min' hne
    have hrun := run_long hg n d 2 (by omega) hne
    have h1 := q_ap hq s d 1 (fun j hj => hrun j (by omega))
    have h2 := q_ap hq s d 2 (fun j hj => hrun j (by omega))
    apply hex ⟨s, ?_, by simpa using hrun 0 (by omega)⟩
    have e : ∀ x, x.Prime → x % 3 = 0 → x = 3 := fun x hx h3 =>
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hx).mp (Nat.dvd_of_mod_eq_zero h3)).symm
    have e0 := e _ (hp s)
    have e1 := e _ (hp (s + 1))
    have e2 := e _ (hp (s + 2))
    rw [h1, one_mul] at e1; rw [h2] at e2
    have := (hp s).two_le
    clear_value s
    have hcases : q s % 3 = 0 ∨ (q s + d) % 3 = 0 ∨ (q s + 2 * d) % 3 = 0 := by
      have h3' : d % 3 ≠ 0 := fun h => hd3 (Nat.dvd_of_mod_eq_zero h)
      generalize q s = a
      have ha : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hd' : d % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have e1 : (a + d) % 3 = (a % 3 + d % 3) % 3 := Nat.add_mod _ _ _
      have e2 : (a + 2 * d) % 3 = (a % 3 + (2 * d) % 3) % 3 := Nat.add_mod _ _ _
      have e3 : (2 * d) % 3 = (2 % 3 * (d % 3)) % 3 := Nat.mul_mod _ _ _
      rw [e1, e2, e3]
      interval_cases (a % 3) <;> interval_cases (d % 3) <;> simp_all
    rcases hcases with h | h | h
    · exact e0 h
    · have := e1 h; omega
    · have := e2 h; omega

lemma gen_bound {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (n d : ℕ) (hd : 1 ≤ d) :
    (S q n d).card ≤ ((Finset.Icc 1 d).filter (fun m => primorial m ∣ d)).card := by
  have hex : ∃ p, p.Prime ∧ ¬ p ∣ d := by
    refine ⟨(d + 1).minFac, Nat.minFac_prime (by omega), fun h => ?_⟩
    have h2 := Nat.minFac_dvd (d + 1)
    have := (Nat.dvd_add_right h).mp h2
    exact (Nat.minFac_prime (show d + 1 ≠ 1 by omega)).one_lt.ne' (Nat.dvd_one.mp this)
  classical
  set p := Nat.find hex
  have hpP : p.Prime ∧ ¬ p ∣ d := Nat.find_spec hex
  have hp1 : p ≤ d + 1 := by
    have hm : (d + 1).minFac.Prime ∧ ¬ (d + 1).minFac ∣ d := by
      refine ⟨Nat.minFac_prime (by omega), fun h => ?_⟩
      have := (Nat.dvd_add_right h).mp (Nat.minFac_dvd (d + 1))
      exact (Nat.minFac_prime (show d + 1 ≠ 1 by omega)).one_lt.ne' (Nat.dvd_one.mp this)
    exact (Nat.find_min' hex hm).trans (Nat.minFac_le (by omega))
  have hb := run_bound hq hp hg n d p hd hpP.1 hpP.2 hp1
  refine hb.trans ?_
  have hsub : Finset.Icc 1 (p - 1) ⊆ (Finset.Icc 1 d).filter (fun m => primorial m ∣ d) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hm.1, by omega⟩, ?_⟩
    unfold primorial
    apply Finset.prod_primes_dvd
    · intro a ha; exact (Finset.mem_filter.mp ha).2.prime
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hlt : a < p := by have := Finset.mem_range.mp ha'.1; omega
      by_contra hna
      exact Nat.find_min hex hlt ⟨ha'.2, hna⟩
  calc p - 1 = (Finset.Icc 1 (p - 1)).card := by simp
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
lemma uniq {q : ℕ → ℕ} (hq : StrictMono q) (T : Finset ℕ) (c : ℕ) :
    (T.filter (fun d => ∃ i, q i = c ∧ g q i = d)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨j, hj, rfl⟩ := (Finset.mem_filter.mp hb).2
  rw [hq.injective (hi.trans hj.symm)]

lemma prim_double (n : ℕ) (hn : n ≠ 0) : primorial n * (n + 1) ≤ primorial (2 * n) := by
  obtain ⟨r, hr, hnr, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  rw [two_mul, primorial_add]
  apply Nat.mul_le_mul_left
  have hmem : r ∈ (Finset.Ico (n + 1) (n + n + 1)).filter Nat.Prime := by
    simp only [Finset.mem_filter, Finset.mem_Ico]; refine ⟨⟨by omega, by omega⟩, hr⟩
  calc n + 1 ≤ r := hnr
    _ ≤ ∏ p ∈ (Finset.Ico (n + 1) (n + n + 1)).filter Nat.Prime, p :=
      Finset.single_le_prod' (fun p hp => (Finset.mem_filter.mp hp).2.one_lt.le) hmem

lemma prim_five : primorial 5 = 30 := by decide
lemma prim_seven : primorial 7 = 210 := by decide

lemma prim_sq (m : ℕ) (hm : 20 ≤ m) : 3 * m ^ 2 ≤ primorial m := by
  set n1 := m / 2
  set n2 := n1 / 2
  have h1 : primorial n1 * (n1 + 1) ≤ primorial m :=
    (prim_double n1 (by omega)).trans (primorial_mono (by omega))
  have h2 : primorial n2 * (n2 + 1) ≤ primorial n1 :=
    (prim_double n2 (by omega)).trans (primorial_mono (by omega))
  have h3 : 30 ≤ primorial n2 := prim_five ▸ primorial_mono (by omega)
  have e1 : m + 1 ≤ 2 * (n1 + 1) := by omega
  have e2 : m + 1 ≤ 4 * (n2 + 1) := by omega
  have : 30 * (n2 + 1) * (n1 + 1) ≤ primorial m := by
    calc 30 * (n2 + 1) * (n1 + 1) ≤ primorial n2 * (n2 + 1) * (n1 + 1) := by gcongr
      _ ≤ primorial n1 * (n1 + 1) := by gcongr
      _ ≤ _ := h1
  nlinarith

/-- the bound function -/
noncomputable def bnd (m : ℕ) : ℝ :=
  if m ≤ 6 then 1 / 30 else if m ≤ 19 then 1 / 210 else (1 / 3) * (1 / ((m : ℝ) - 1) - 1 / m)

lemma inv_prim_le (m : ℕ) (hm : 5 ≤ m) : (1 : ℝ) / primorial m ≤ bnd m := by
  unfold bnd
  split_ifs with h6 h19
  · have : (30 : ℝ) ≤ primorial m := by exact_mod_cast prim_five ▸ primorial_mono hm
    gcongr
  · have : (210 : ℝ) ≤ primorial m := by
      have h := primorial_mono (show 7 ≤ m by omega)
      rw [prim_seven] at h; exact_mod_cast h
    gcongr
  · have hsq : (3 : ℝ) * m ^ 2 ≤ primorial m := by exact_mod_cast prim_sq m (by omega)
    have hm1 : (19 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (20 : ℝ) ≤ m := by exact_mod_cast (show 20 ≤ m by omega)
      linarith
    have hmpos : (0 : ℝ) < m := by linarith
    rw [show (1 : ℝ) / 3 * (1 / ((m : ℝ) - 1) - 1 / m) = 1 / (3 * (m * ((m : ℝ) - 1))) by
      field_simp; ring]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

lemma bnd_sum (D : ℕ) (hD : 19 ≤ D) :
    ∑ m ∈ Finset.Icc 5 D, bnd m = 2 / 30 + 13 / 210 + (1 / 3) * (1 / 19 - 1 / (D : ℝ)) := by
  induction D, hD using Nat.le_induction with
  | base => simp only [bnd]; norm_num [Finset.sum_Icc_succ_top]
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [bnd, show ¬ k + 1 ≤ 6 by omega, show ¬ k + 1 ≤ 19 by omega, if_false]
    push_cast
    simp only [add_sub_cancel_right]
    have : (19 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    have hk1 : (k : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring

lemma tail (D : ℕ) : ∑ m ∈ Finset.Icc 5 D, (1 : ℝ) / primorial m ≤ 3 / 20 := by
  have hb : ∀ m, 5 ≤ m → 0 ≤ bnd m := fun m hm =>
    le_trans (by positivity) (inv_prim_le m hm)
  calc ∑ m ∈ Finset.Icc 5 D, (1 : ℝ) / primorial m
      ≤ ∑ m ∈ Finset.Icc 5 D, bnd m :=
        Finset.sum_le_sum fun m hm => inv_prim_le m (Finset.mem_Icc.mp hm).1
    _ ≤ ∑ m ∈ Finset.Icc 5 (max D 19), bnd m :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc le_rfl (le_max_left _ _))
          (fun m hm _ => hb m (Finset.mem_Icc.mp hm).1)
    _ = 2 / 30 + 13 / 210 + (1 / 3) * (1 / 19 - 1 / ((max D 19 : ℕ) : ℝ)) :=
        bnd_sum _ (le_max_right _ _)
    _ ≤ 3 / 20 := by
        have : (0 : ℝ) ≤ 1 / ((max D 19 : ℕ) : ℝ) := by positivity
        linarith


lemma count_mul (D k : ℕ) (hk : 0 < k) :
    (((Finset.Icc 1 D).filter (fun d => k ∣ d)).card : ℝ) ≤ D / k := by
  have h := Nat.Ioc_filter_dvd_card_eq_div D k
  rw [show Finset.Icc 1 D = Finset.Ioc 0 D by ext; simp; omega, h]
  rw [le_div_iff₀ (by exact_mod_cast hk)]
  exact_mod_cast Nat.div_mul_le_self D k

lemma count_2not3 (D : ℕ) :
    (((Finset.Icc 1 D).filter (fun d => 2 ∣ d ∧ ¬ 3 ∣ d)).card : ℝ) ≤ D / 3 + 1 := by
  have hI : Finset.Icc 1 D = Finset.Ioc 0 D := by ext; simp; omega
  have h2 := Nat.Ioc_filter_dvd_card_eq_div D 2
  have h6 := Nat.Ioc_filter_dvd_card_eq_div D 6
  have hsplit : ((Finset.Ioc 0 D).filter (fun d => 2 ∣ d)) =
      ((Finset.Ioc 0 D).filter (fun d => 2 ∣ d ∧ ¬ 3 ∣ d)) ∪
      ((Finset.Ioc 0 D).filter (fun d => 6 ∣ d)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, h2⟩
      by_cases h3 : 3 ∣ x
      · exact Or.inr ⟨hx, Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3⟩
      · exact Or.inl ⟨hx, h2, h3⟩
    · rintro (⟨hx, h2, _⟩ | ⟨hx, h6⟩)
      · exact ⟨hx, h2⟩
      · exact ⟨hx, dvd_trans (by norm_num) h6⟩
  have hdisj : Disjoint ((Finset.Ioc 0 D).filter (fun d => 2 ∣ d ∧ ¬ 3 ∣ d))
      ((Finset.Ioc 0 D).filter (fun d => 6 ∣ d)) := by
    rw [Finset.disjoint_filter]; intro x _ h1 h6
    exact h1.2 (dvd_trans (by norm_num) h6)
  have hc := Finset.card_union_of_disjoint hdisj
  rw [← hsplit, h2, h6] at hc
  rw [hI]
  have hA : ((((Finset.Ioc 0 D).filter (fun d => 2 ∣ d ∧ ¬ 3 ∣ d)).card : ℕ) : ℝ)
      = ((D / 2 : ℕ) : ℝ) - ((D / 6 : ℕ) : ℝ) := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast hc.symm
  rw [hA]
  have e1 : ((D / 2 : ℕ) : ℝ) ≤ D / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self D 2
  have e2 : (D : ℝ) / 6 - 1 ≤ ((D / 6 : ℕ) : ℝ) := by
    have : D < (D / 6 + 1) * 6 := by omega
    have : (D : ℝ) < ((D / 6 : ℕ) + 1) * 6 := by exact_mod_cast this
    linarith
  linarith

open Classical in
lemma count_main {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (n D : ℕ) :
    ((((Finset.range n).filter (fun i => g q i ≤ D)).card : ℕ) : ℝ) ≤ 3 + (23 / 20) * D := by
  -- fibres
  have hfib : ((Finset.range n).filter (fun i => g q i ≤ D)).card ≤
      ∑ d ∈ Finset.Icc 1 D, (S q n d).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := g q) (t := Finset.Icc 1 D)]
    · apply Finset.sum_le_sum; intro d _
      apply Finset.card_le_card; intro x hx
      simp only [S, Finset.mem_filter] at hx ⊢; exact ⟨hx.1.1, hx.2⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
      have := hq (show x < x + 1 by omega)
      have hx2 : 1 ≤ g q x ∧ g q x ≤ D := by unfold g at hx ⊢; omega
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr hx2)
  set E2 : ℕ → ℕ := fun d => if (∃ i, q i = 2 ∧ g q i = d) then 1 else 0
  set E3 : ℕ → ℕ := fun d => if (∃ i, q i = 3 ∧ g q i = d) then 1 else 0
  set A : ℕ → ℕ := fun d => if 2 ∣ d ∧ ¬ 3 ∣ d then 1 else 0
  set B : ℕ → ℕ := fun d => if 6 ∣ d then ((Finset.Icc 1 D).filter (fun m => primorial m ∣ d)).card
    else 0
  have hpt : ∀ d ∈ Finset.Icc 1 D, (S q n d).card ≤ E2 d + E3 d + A d + B d := by
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    by_cases h2 : 2 ∣ d
    · by_cases h3 : 3 ∣ d
      · have h6 : 6 ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
        have := gen_bound hq hp hg n d hd'.1
        have hsub : (Finset.Icc 1 d).filter (fun m => primorial m ∣ d) ⊆
            (Finset.Icc 1 D).filter (fun m => primorial m ∣ d) :=
          Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hd'.2)
        have := Finset.card_le_card hsub
        simp only [B, if_pos h6]; omega
      · have := three_bound hq hp hg n d h2 h3
        simp only [A, E3, if_pos (And.intro h2 h3)]; omega
    · have := odd_bound hq hp hg n d h2
      simp only [E2]; omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hE2 : ∑ d ∈ Finset.Icc 1 D, E2 d ≤ 1 := by
    simp only [E2]; rw [Finset.sum_boole]; exact_mod_cast uniq hq _ 2
  have hE3 : ∑ d ∈ Finset.Icc 1 D, E3 d ≤ 1 := by
    simp only [E3]; rw [Finset.sum_boole]; exact_mod_cast uniq hq _ 3
  have hA : ((∑ d ∈ Finset.Icc 1 D, A d : ℕ) : ℝ) ≤ D / 3 + 1 := by
    simp only [A]; rw [Finset.sum_boole]; exact_mod_cast count_2not3 D
  -- the B sum: swap
  have hBswap : ∑ d ∈ Finset.Icc 1 D, B d = ∑ m ∈ Finset.Icc 1 D,
      ((Finset.Icc 1 D).filter (fun d => 6 ∣ d ∧ primorial m ∣ d)).card := by
    simp only [B, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m _
    by_cases h6 : 6 ∣ m <;> simp [h6]
  have hBm : ∀ m ∈ Finset.Icc 1 D,
      ((((Finset.Icc 1 D).filter (fun d => 6 ∣ d ∧ primorial m ∣ d)).card : ℕ) : ℝ) ≤
        if m ≤ 4 then (D : ℝ) / 6 else D * (1 / primorial m) := by
    intro m _
    split_ifs with hm4
    · refine le_trans ?_ (count_mul D 6 (by norm_num))
      exact_mod_cast Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩)
    · rw [mul_one_div]
      refine le_trans ?_ (count_mul D (primorial m) (primorial_pos m))
      exact_mod_cast Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
  have hB : ((∑ d ∈ Finset.Icc 1 D, B d : ℕ) : ℝ) ≤ 4 * ((D : ℝ) / 6) + D * (3 / 20) := by
    rw [hBswap]; push_cast
    refine (Finset.sum_le_sum hBm).trans ?_
    rw [Finset.sum_ite]
    gcongr
    · rw [Finset.sum_const, nsmul_eq_mul]
      have : ((Finset.Icc 1 D).filter (fun m => m ≤ 4)).card ≤ 4 := by
        calc _ ≤ (Finset.Icc 1 4).card := Finset.card_le_card (by
              intro x hx; simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢; omega)
          _ = 4 := by simp
      have : (((Finset.Icc 1 D).filter (fun m => m ≤ 4)).card : ℝ) ≤ 4 := by exact_mod_cast this
      have : (0 : ℝ) ≤ D / 6 := by positivity
      nlinarith
    · rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine le_trans ?_ (tail D)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx; simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢; omega
      · intro _ _ _; positivity
  have hfibR : ((((Finset.range n).filter (fun i => g q i ≤ D)).card : ℕ) : ℝ) ≤
      ((∑ d ∈ Finset.Icc 1 D, E2 d : ℕ) : ℝ) + ((∑ d ∈ Finset.Icc 1 D, E3 d : ℕ) : ℝ) +
      ((∑ d ∈ Finset.Icc 1 D, A d : ℕ) : ℝ) + ((∑ d ∈ Finset.Icc 1 D, B d : ℕ) : ℝ) := by
    exact_mod_cast hfib.trans hsum
  have hE2' : ((∑ d ∈ Finset.Icc 1 D, E2 d : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hE2
  have hE3' : ((∑ d ∈ Finset.Icc 1 D, E3 d : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hE3
  linarith


lemma gap_lower {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (i : ℕ) : ((i : ℝ) - 2) / (23 / 20) ≤ g q i := by
  have h := count_main hq hp hg (i + 1) (g q i)
  have hfull : (Finset.range (i + 1)).filter (fun j => g q j ≤ g q i) = Finset.range (i + 1) := by
    apply Finset.filter_true_of_mem
    intro j hj; exact hg (by have := Finset.mem_range.mp hj; omega)
  rw [hfull, Finset.card_range] at h
  push_cast at h
  rw [div_le_iff₀ (by norm_num)]
  linarith

lemma q_sum {q : ℕ → ℕ} (hq : StrictMono q) (n : ℕ) : q n = q 0 + ∑ i ∈ Finset.range n, g q i := by
  induction n with
  | zero => simp
  | succ k ih => rw [q_succ hq, ih, Finset.sum_range_succ]; ring

lemma sum_id (n : ℕ) : ∑ i ∈ Finset.range n, (((i : ℝ) - 2) / (23 / 20)) =
    ((n : ℝ) * (n - 1) / 2 - 2 * n) / (23 / 20) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma q_lower {q : ℕ → ℕ} (hq : StrictMono q) (hp : ∀ n, (q n).Prime) (hg : Monotone (g q))
    (n : ℕ) (hn : 100 ≤ n) : (9 / 25 : ℝ) * n ^ 2 ≤ q n := by
  have h1 : (q n : ℝ) = q 0 + ∑ i ∈ Finset.range n, (g q i : ℝ) := by
    rw [q_sum hq n]; push_cast; ring
  have h2 : ∑ i ∈ Finset.range n, (((i : ℝ) - 2) / (23 / 20)) ≤ ∑ i ∈ Finset.range n, (g q i : ℝ) :=
    Finset.sum_le_sum fun i _ => gap_lower hq hp hg i
  rw [sum_id] at h2
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ q 0 := by positivity
  have : (9 / 25 : ℝ) * n ^ 2 ≤ ((n : ℝ) * (n - 1) / 2 - 2 * n) / (23 / 20) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  linarith

theorem main : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    Filter.liminf (fun n : ℕ => (q n : ENNReal) / n ^ 2) Filter.atTop > 0.352 := by
  intro q hq h
  have hp : ∀ n, (q n).Prime := fun n => (h n).1
  have hg : Monotone (g q) := by
    apply monotone_nat_of_le_succ
    intro n; have := (h n).2; unfold g; omega
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (9 / 25) ≤ (q n : ENNReal) / n ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 100] with n hn
    have hpos : (0 : ℝ) < n := by have : (100 : ℝ) ≤ n := by exact_mod_cast hn
                                  linarith
    have hl := q_lower hq hp hg n hn
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
    have : ENNReal.ofReal (9 / 25) * (n : ENNReal) ^ 2 = ENNReal.ofReal ((9 / 25) * (n : ℝ) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    rw [this, show (q n : ENNReal) = ENNReal.ofReal (q n : ℝ) by rw [ENNReal.ofReal_natCast]]
    exact ENNReal.ofReal_le_ofReal hl
  have hlim : ENNReal.ofReal (9 / 25) ≤ Filter.liminf (fun n : ℕ => (q n : ENNReal) / n ^ 2) Filter.atTop :=
    Filter.le_liminf_of_le (by isBoundedDefault) hev
  refine lt_of_lt_of_le ?_ hlim
  have e : (0.352 : ENNReal) = ENNReal.ofReal 0.352 := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    rfl
  rw [e, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end E455

theorem OMA.solution : type_of% @Erdos455.erdos_455.variants.liminf := E455.main
