import OMAStatements.S_mo_315485

open OMA.S_mo_315485

namespace DivisibilityPartitions

lemma isPartition_nil_iff (n : ℕ) : IsPartition n 0 [] ↔ n = 0 := by
  unfold IsPartition
  simp [eq_comm]

lemma isPartition_cons_iff {n k d : ℕ} {t : List ℕ} :
    IsPartition n (k + 1) (d :: t) ↔
      n ≠ 0 ∧ 0 < d ∧ d ∣ n ∧ ∃ t' : List ℕ,
        t = t'.map (d * ·) ∧ IsPartition (n / d - 1) k t' ∧ ∀ a ∈ t', 2 ≤ a := by
  unfold IsPartition
  constructor
  · rintro ⟨hsum, hlen, hpos, hpw⟩
    rw [List.pairwise_cons] at hpw
    rcases hpw with ⟨hhead, htail⟩
    have hd_pos : 0 < d := hpos d (by simp)
    have hn_ne : n ≠ 0 := by
      rw [← hsum, List.sum_cons]
      omega
    have ht_dvd : ∀ a ∈ t, d ∣ a := fun a ha ↦ (hhead a ha).2
    have hsum_dvd : d ∣ t.sum := List.dvd_sum ht_dvd
    have hn_dvd : d ∣ n := by
      rw [← hsum, List.sum_cons]
      exact dvd_add dvd_rfl hsum_dvd
    let t' : List ℕ := t.map (· / d)
    have ht_eq : t = t'.map (d * ·) := by
      dsimp [t']
      rw [List.map_map]
      symm
      calc
        List.map ((d * ·) ∘ (· / d)) t = List.map id t :=
          List.map_congr_left fun a ha ↦ Nat.mul_div_cancel' (ht_dvd a ha)
        _ = t := List.map_id t
    have hsum_t : t.sum = d * t'.sum := by
      conv_lhs => rw [ht_eq]
      rw [List.sum_map_mul_left]
      simp only [List.map_id']
    have hsum_t' : t'.sum = n / d - 1 := by
      have h1 : d + d * t'.sum = n := by simpa [List.sum_cons, hsum_t] using hsum
      have h2 : d * (1 + t'.sum) = n := by linarith
      have h3 : 1 + t'.sum = n / d := by
        rw [← h2, Nat.mul_div_cancel_left _ hd_pos]
      omega
    have hlen' : t'.length = k := by
      dsimp [t']; simp only [List.length_map]; simpa using hlen
    have hge2 : ∀ a ∈ t', 2 ≤ a := by
      intro a ha
      dsimp [t'] at ha
      rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
      have hlt : d < b := (hhead b hb).1
      have hdvd : d ∣ b := (hhead b hb).2
      have hmul : d * (b / d) = b := Nat.mul_div_cancel' hdvd
      by_contra hlt2
      have hle1 : b / d ≤ 1 := by omega
      have : b ≤ d := by nlinarith
      omega
    have hpos' : ∀ a ∈ t', 0 < a := fun a ha ↦ by have := hge2 a ha; omega
    have hpw' : t'.Pairwise (fun a b ↦ a < b ∧ a ∣ b) := by
      rw [ht_eq, List.pairwise_map] at htail
      refine htail.imp fun {a b} ⟨hlt, hdvd⟩ ↦ ?_
      refine ⟨Nat.lt_of_mul_lt_mul_left hlt, ?_⟩
      exact (Nat.mul_dvd_mul_iff_left hd_pos).mp hdvd
    exact ⟨hn_ne, hd_pos, hn_dvd, t', ht_eq, ⟨hsum_t', hlen', hpos', hpw'⟩, hge2⟩
  · rintro ⟨hn_ne, hd_pos, hn_dvd, t', rfl, ⟨hsum', hlen', hpos', hpw'⟩, hge2⟩
    have hn_ge_d : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn_ne) hn_dvd
    have hdiv_pos : 1 ≤ n / d := Nat.div_pos hn_ge_d hd_pos
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.sum_cons, List.sum_map_mul_left]
      simp only [List.map_id']
      rw [hsum']
      have h1 : d + d * (n / d - 1) = d * (n / d) := by
        have : 1 + (n / d - 1) = n / d := by omega
        calc
          d + d * (n / d - 1) = d * (1 + (n / d - 1)) := by ring
          _ = d * (n / d) := by rw [this]
      rw [h1, Nat.mul_div_cancel' hn_dvd]
    · simp [hlen']
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hd_pos
      · rcases List.mem_map.mp ha' with ⟨b, hb, rfl⟩
        exact Nat.mul_pos hd_pos (hpos' b hb)
    · rw [List.pairwise_cons]
      refine ⟨fun a ha ↦ ?_, ?_⟩
      · rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
        have hb2 : 2 ≤ b := hge2 b hb
        refine ⟨?_, dvd_mul_right d b⟩
        nlinarith
      · rw [List.pairwise_map]
        refine hpw'.imp fun {a b} ⟨hlt, hdvd⟩ ↦ ?_
        exact ⟨Nat.mul_lt_mul_of_pos_left hlt hd_pos, mul_dvd_mul_left d hdvd⟩

lemma mem_partitions_iff (lo : ℕ) (hlo : 1 ≤ lo) (k n : ℕ) (l : List ℕ) :
    l ∈ partitions lo k n ↔ IsPartition n k l ∧ ∀ a ∈ l, lo ≤ a := by
  induction k generalizing lo n l with
  | zero =>
    unfold partitions
    by_cases hn : n = 0
    · subst hn
      simp only [if_true, Finset.mem_singleton]
      constructor
      · rintro rfl; exact ⟨(isPartition_nil_iff 0).mpr rfl, by simp⟩
      · rintro ⟨⟨_, hlen, _, _⟩, _⟩
        exact List.eq_nil_of_length_eq_zero hlen
    · simp only [if_neg hn, Finset.notMem_empty, false_iff]
      rintro ⟨⟨hsum, hlen, _, _⟩, _⟩
      have hnil : l = [] := List.eq_nil_of_length_eq_zero hlen
      subst hnil
      simp at hsum
      exact hn hsum.symm
  | succ k ih =>
    unfold partitions
    simp only [Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨d, ⟨⟨hdvd, hn_ne⟩, hlo_d⟩, t', ht', rfl⟩
      have hd_pos : 0 < d := by omega
      have hih := (ih 2 (by omega) (n / d - 1) t').mp ht'
      have hpart : IsPartition n (k + 1) (d :: t'.map (d * ·)) :=
        isPartition_cons_iff.mpr ⟨hn_ne, hd_pos, hdvd, t', rfl, hih.1, hih.2⟩
      refine ⟨hpart, fun a ha ↦ ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hlo_d
      · rcases List.mem_map.mp ha' with ⟨b, hb, rfl⟩
        have hb2 : 2 ≤ b := hih.2 b hb
        nlinarith
    · rintro ⟨hpart, hge⟩
      cases l with
      | nil =>
        have hlen := hpart.2.1
        simp at hlen
      | cons d t =>
        rcases isPartition_cons_iff.mp hpart with ⟨hn_ne, hd_pos, hdvd, t', rfl, hpart', hge2⟩
        refine ⟨d, ⟨⟨hdvd, hn_ne⟩, hge d (by simp)⟩, t', ?_, rfl⟩
        exact (ih 2 (by omega) (n / d - 1) t').mpr ⟨hpart', hge2⟩

lemma card_partitions_eq_count (lo : ℕ) (hlo : 1 ≤ lo) (k n : ℕ) :
    (partitions lo k n).card = count lo k n := by
  induction k generalizing lo n with
  | zero =>
    unfold partitions count
    by_cases hn : n = 0 <;> simp [hn]
  | succ k ih =>
    unfold partitions count
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hlo_d : lo ≤ d := (Finset.mem_filter.mp hd).2
      have hd_pos : 0 < d := by omega
      rw [Finset.card_image_of_injective]
      · exact ih 2 (by omega) (n / d - 1)
      · intro l₁ l₂ heq
        have htail : l₁.map (d * ·) = l₂.map (d * ·) := List.cons.inj heq |>.2
        exact List.map_injective_iff.mpr (fun a b h ↦ Nat.eq_of_mul_eq_mul_left hd_pos h) htail
    · intro d₁ _ d₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro l h1 h2
      rcases Finset.mem_image.mp h1 with ⟨l₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨l₂, _, heq⟩
      exact hne (List.cons.inj heq).1.symm

lemma isPartition_map_mul {n k c : ℕ} {l : List ℕ} (hc : 0 < c) (hl : IsPartition n k l) :
    IsPartition (c * n) k (l.map (c * ·)) := by
  rcases hl with ⟨hsum, hlen, hpos, hpw⟩
  refine ⟨?_, by simp [hlen], ?_, ?_⟩
  · rw [List.sum_map_mul_left]
    simp only [List.map_id']
    rw [hsum]
  · intro a ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact Nat.mul_pos hc (hpos b hb)
  · rw [List.pairwise_map]
    exact hpw.imp fun {a b} ⟨hlt, hdvd⟩ ↦
      ⟨Nat.mul_lt_mul_of_pos_left hlt hc, mul_dvd_mul_left c hdvd⟩

def powFourPart : ℕ → List ℕ
  | 0 => [1, 3]
  | k + 1 => powFourPart k ++ [3 * 4 ^ (k + 1)]

lemma powFourPart_spec (k : ℕ) :
    IsPartition (2 ^ (2 * (k + 1))) (k + 2) (powFourPart k) ∧
      ∀ a ∈ powFourPart k, a ≤ 3 * 4 ^ k ∧ a ∣ 3 * 4 ^ k := by
  induction k with
  | zero =>
    refine ⟨⟨by norm_num [powFourPart], by simp [powFourPart], ?_, ?_⟩, ?_⟩
    · intro a ha; simp [powFourPart] at ha; rcases ha with rfl | rfl <;> omega
    · simp [powFourPart]
    · intro a ha; simp [powFourPart] at ha; rcases ha with rfl | rfl <;> norm_num
  | succ k ih =>
    rcases ih with ⟨⟨hsum, hlen, hpos, hpw⟩, hbound⟩
    have hpow_eq : 2 ^ (2 * (k + 1)) = 4 ^ (k + 1) := by
      rw [pow_mul]; norm_num
    have hpow_eq2 : 2 ^ (2 * (k + 2)) = 4 ^ (k + 2) := by
      rw [pow_mul]; norm_num
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [powFourPart, List.sum_append, List.sum_singleton, hsum, hpow_eq, hpow_eq2]
      ring
    · simp [powFourPart, hlen]
    · intro a ha
      simp only [powFourPart, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hpos a ha
      · positivity
    · simp only [powFourPart, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
      refine ⟨hpw, trivial, fun a ha b hb ↦ ?_⟩
      subst hb
      rcases hbound a ha with ⟨hle, hdvd⟩
      have hlt : 3 * 4 ^ k < 3 * 4 ^ (k + 1) := by
        have hpos4 : 0 < 4 ^ k := by positivity
        rw [pow_succ]; linarith
      have hdvd4 : 3 * 4 ^ k ∣ 3 * 4 ^ (k + 1) := by
        rw [pow_succ]; exact ⟨4, by ring⟩
      exact ⟨lt_of_le_of_lt hle hlt, hdvd.trans hdvd4⟩
    · intro a ha
      simp only [powFourPart, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · rcases hbound a ha with ⟨hle, hdvd⟩
        have hle4 : 3 * 4 ^ k ≤ 3 * 4 ^ (k + 1) := by
          rw [pow_succ]; linarith [show 0 ≤ 4 ^ k from Nat.zero_le _]
        have hdvd4 : 3 * 4 ^ k ∣ 3 * 4 ^ (k + 1) := by
          rw [pow_succ]; exact ⟨4, by ring⟩
        exact ⟨hle.trans hle4, hdvd.trans hdvd4⟩
      · exact ⟨le_rfl, dvd_rfl⟩

lemma cutoff_pos (k : ℕ) : 0 < cutoff k := by
  induction k with
  | zero => simp [cutoff]
  | succ k _ =>
    unfold cutoff
    positivity

lemma exists_partition_of_cutoff (n k : ℕ) (hn : cutoff k ≤ n) :
    ∃ l : List ℕ, IsPartition n (k + 1) l := by
  induction k generalizing n with
  | zero =>
    refine ⟨[n], ?_, by simp, ?_, by simp⟩
    · simp
    · intro a ha
      simp only [List.mem_singleton] at ha
      rw [ha]
      have : 1 ≤ n := by simpa [cutoff] using hn
      omega
  | succ k ih =>
    have hn_pos : 0 < n := lt_of_lt_of_le (cutoff_pos (k + 1)) hn
    have hn_ne : n ≠ 0 := hn_pos.ne'
    let a : ℕ := n.factorization 2
    let u : ℕ := n / 2 ^ a
    have h2a_dvd : 2 ^ a ∣ n := Nat.ordProj_dvd n 2
    have hn_eq : 2 ^ a * u = n := Nat.mul_div_cancel' h2a_dvd
    have hu_pos : 0 < u :=
      Nat.pos_of_ne_zero fun hu0 ↦ by rw [hu0, mul_zero] at hn_eq; exact hn_ne hn_eq.symm
    have hu_odd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hn_ne
    by_cases ha : 2 * (k + 1) ≤ a
    · have hdvd : 2 ^ (2 * (k + 1)) ∣ n := (pow_dvd_pow 2 ha).trans h2a_dvd
      let q : ℕ := n / 2 ^ (2 * (k + 1))
      have hq_mul : q * 2 ^ (2 * (k + 1)) = n := Nat.div_mul_cancel hdvd
      have hq_pos : 0 < q :=
        Nat.pos_of_ne_zero fun hq0 ↦ by rw [hq0, zero_mul] at hq_mul; exact hn_ne hq_mul.symm
      refine ⟨(powFourPart k).map (q * ·), ?_⟩
      have hpart := isPartition_map_mul hq_pos (powFourPart_spec k).1
      rwa [hq_mul] at hpart
    · push Not at ha
      have h2a_lt : 2 ^ a < 2 ^ (2 * (k + 1)) := Nat.pow_lt_pow_right (by norm_num) ha
      have hu_ge : 2 * cutoff k + 1 ≤ u := by
        unfold cutoff at hn
        by_contra hlt
        push Not at hlt
        have h1 : 2 ^ a * u < 2 ^ (2 * (k + 1)) * (2 * cutoff k + 1) := by
          calc
            2 ^ a * u < 2 ^ (2 * (k + 1)) * u := Nat.mul_lt_mul_of_pos_right h2a_lt hu_pos
            _ ≤ 2 ^ (2 * (k + 1)) * (2 * cutoff k + 1) :=
                Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
        omega
      let m : ℕ := u / 2
      have hu_eq : u = 2 * m + 1 := by omega
      have hm_ge : cutoff k ≤ m := by omega
      obtain ⟨l, hl⟩ := ih m hm_ge
      have hu_part : IsPartition u (k + 2) (1 :: l.map (2 * ·)) := by
        refine isPartition_cons_iff.mpr ⟨hu_pos.ne', by omega, one_dvd u, l.map (2 * ·), ?_, ?_, ?_⟩
        · simp
        · have hdiv : u / 1 - 1 = 2 * m := by omega
          rw [hdiv]
          exact isPartition_map_mul (by omega) hl
        · intro x hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          have hy_pos : 0 < y := hl.2.2.1 y hy
          omega
      refine ⟨(1 :: l.map (2 * ·)).map (2 ^ a * ·), ?_⟩
      have hpart := isPartition_map_mul (by positivity : 0 < 2 ^ a) hu_part
      rwa [hn_eq] at hpart

lemma nat_geom_step (c k : ℕ) : c + (2 * c) * (2 ^ k - 1) = c * (2 ^ (k + 1) - 1) := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have h2 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by norm_num)
  zify [h1, h2]
  ring

def powTwoFrom (c : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => c :: powTwoFrom (2 * c) k

lemma dvd_of_mem_powTwoFrom {c k a : ℕ} (ha : a ∈ powTwoFrom c k) : c ∣ a := by
  induction k generalizing c with
  | zero => simp [powTwoFrom] at ha
  | succ k ih =>
    simp only [powTwoFrom, List.mem_cons] at ha
    rcases ha with rfl | ha'
    · exact dvd_rfl
    · exact (dvd_mul_left c 2).trans (ih ha')

lemma powTwoFrom_spec (c k : ℕ) (hc : 0 < c) :
    IsPartition (c * (2 ^ k - 1)) k (powTwoFrom c k) ∧
      ∀ a ∈ powTwoFrom c k, c ≤ a ∧ a < c * 2 ^ k ∧ a ∣ c * 2 ^ k := by
  induction k generalizing c with
  | zero =>
    simp [powTwoFrom, isPartition_nil_iff]
  | succ k ih =>
    rcases ih (2 * c) (by omega) with ⟨⟨hsum, hlen, hpos, hpw⟩, hbound⟩
    have hsum_eq : c + (2 * c) * (2 ^ k - 1) = c * (2 ^ (k + 1) - 1) := nat_geom_step c k
    refine ⟨⟨?_, by simp [powTwoFrom, hlen], ?_, ?_⟩, ?_⟩
    · simp only [powTwoFrom, List.sum_cons, hsum, hsum_eq]
    · intro a ha
      simp only [powTwoFrom, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hc
      · exact hpos a ha
    · simp only [powTwoFrom, List.pairwise_cons]
      refine ⟨fun b hb ↦ ?_, hpw⟩
      have hge := (hbound b hb).1
      have hdvd : c ∣ b := (dvd_mul_left c 2).trans (dvd_of_mem_powTwoFrom hb)
      exact ⟨by omega, hdvd⟩
    · intro a ha
      simp only [powTwoFrom, List.mem_cons] at ha
      rcases ha with ha_eq | ha
      · rw [ha_eq]
        refine ⟨le_rfl, ?_, dvd_mul_right c (2 ^ (k + 1))⟩
        have hgt : 1 < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
        nlinarith
      · rcases hbound a ha with ⟨hle, hlt, hdvd⟩
        have heq : 2 * c * 2 ^ k = c * 2 ^ (k + 1) := by ring
        rw [heq] at hlt hdvd
        exact ⟨by omega, hlt, hdvd⟩

lemma exists_mul_many_partitions (k b : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → M ∣ n → b ≤ count 1 (k + 2) n := by
  let M : ℕ := (2 ^ k - 1) + 2 ^ k * 2 ^ (b + 1)
  have hM_pos : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM_pos, fun n hn hMn ↦ ?_⟩
  let q : ℕ := n / M
  have hqM : q * M = n := Nat.div_mul_cancel hMn
  have hq_pos : 0 < q :=
    Nat.pos_of_ne_zero fun hq0 ↦ by rw [hq0, zero_mul] at hqM; omega
  let f : ℕ → List ℕ := fun j ↦
    (powTwoFrom 1 k ++ [2 ^ k * 2 ^ j, 2 ^ k * (2 ^ (b + 1) - 2 ^ j)]).map (q * ·)
  have hf_mem : ∀ j ∈ Finset.range b, f j ∈ partitions 1 (k + 2) n := by
    intro j hj
    have hjb : j < b := Finset.mem_range.mp hj
    have h2j_pos : 0 < 2 ^ j := by positivity
    have h2j_lt : 2 ^ j < 2 ^ (b + 1) - 2 ^ j := by
      have h1 : 2 ^ (j + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
      have h3 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      omega
    have h2j_dvd : 2 ^ j ∣ 2 ^ (b + 1) - 2 ^ j := by
      have hdvd : 2 ^ j ∣ 2 ^ (b + 1) := pow_dvd_pow 2 (by omega)
      exact Nat.dvd_sub hdvd dvd_rfl
    have hbase : IsPartition M (k + 2)
        (powTwoFrom 1 k ++ [2 ^ k * 2 ^ j, 2 ^ k * (2 ^ (b + 1) - 2 ^ j)]) := by
      rcases powTwoFrom_spec 1 k (by omega) with ⟨⟨hsum, hlen, hpos, hpw⟩, hbound⟩
      rw [one_mul] at hsum
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero, hsum]
        have hadd : 2 ^ j + (2 ^ (b + 1) - 2 ^ j) = 2 ^ (b + 1) := by omega
        dsimp [M]
        calc
          (2 ^ k - 1) + (2 ^ k * 2 ^ j + 2 ^ k * (2 ^ (b + 1) - 2 ^ j))
              = (2 ^ k - 1) + 2 ^ k * (2 ^ j + (2 ^ (b + 1) - 2 ^ j)) := by ring
          _ = (2 ^ k - 1) + 2 ^ k * 2 ^ (b + 1) := by rw [hadd]
      · simp [hlen]
      · intro a ha
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with ha | rfl | rfl
        · exact hpos a ha
        · positivity
        · exact Nat.mul_pos (by positivity) (by omega)
      · rw [List.pairwise_append]
        refine ⟨hpw, ?_, fun a ha x hx ↦ ?_⟩
        · rw [List.pairwise_pair]
          exact ⟨Nat.mul_lt_mul_of_pos_left h2j_lt (by positivity), mul_dvd_mul_left (2 ^ k) h2j_dvd⟩
        · rcases hbound a ha with ⟨_, hlt, hdvd⟩
          rw [one_mul] at hlt hdvd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
            have h2k_le : 2 ^ k ≤ 2 ^ k * 2 ^ j := Nat.le_mul_of_pos_right _ (by omega)
            exact ⟨lt_of_lt_of_le hlt h2k_le, hdvd.trans (dvd_mul_right (2 ^ k) (2 ^ j))⟩
          · have h1 : 1 ≤ 2 ^ (b + 1) - 2 ^ j := by omega
            have h2k_le : 2 ^ k ≤ 2 ^ k * (2 ^ (b + 1) - 2 ^ j) := Nat.le_mul_of_pos_right _ (by omega)
            exact ⟨lt_of_lt_of_le hlt h2k_le, hdvd.trans (dvd_mul_right (2 ^ k) _)⟩
    have hscaled : IsPartition n (k + 2) (f j) := by
      have h := isPartition_map_mul hq_pos hbase
      rwa [hqM] at h
    refine (mem_partitions_iff 1 (by omega) (k + 2) n (f j)).mpr ⟨hscaled, fun a ha ↦ ?_⟩
    have := hscaled.2.2.1 a ha
    omega
  have hf_inj : Set.InjOn f (Finset.range b : Set ℕ) := by
    intro j₁ _ j₂ _ heq
    have hget := congr_arg (fun l : List ℕ ↦ l[k]?) heq
    have hlen : (powTwoFrom 1 k).length = k := (powTwoFrom_spec 1 k (by omega)).1.2.1
    have hval : ∀ j : ℕ, (f j)[k]? = some (q * (2 ^ k * 2 ^ j)) := fun j ↦ by
      dsimp [f]
      rw [List.getElem?_map, List.getElem?_append_right (le_of_eq hlen), hlen, Nat.sub_self,
        List.getElem?_cons_zero]
      rfl
    rw [hval j₁, hval j₂, Option.some.injEq] at hget
    have h2 : 2 ^ j₁ = 2 ^ j₂ :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ k)
        (Nat.eq_of_mul_eq_mul_left hq_pos hget)
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  rw [← card_partitions_eq_count 1 (by omega) (k + 2) n]
  calc
    b = (Finset.range b).card := (Finset.card_range b).symm
    _ = ((Finset.range b).image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (partitions 1 (k + 2) n).card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)

lemma min_sum_and_unique_from (k c n : ℕ) (l : List ℕ) (hc : 0 < c)
    (hl : IsPartition n k l) (hge : ∀ a ∈ l, c ≤ a) :
    c * (2 ^ k - 1) ≤ n ∧ (n = c * (2 ^ k - 1) → l = powTwoFrom c k) := by
  induction k generalizing c n l with
  | zero =>
    have hnil : l = [] := List.eq_nil_of_length_eq_zero hl.2.1
    subst hnil
    have hn0 : n = 0 := (isPartition_nil_iff n).mp hl
    subst hn0
    simp [powTwoFrom]
  | succ k ih =>
    cases l with
    | nil =>
      have hlen := hl.2.1
      simp at hlen
    | cons d t =>
      rcases hl with ⟨hsum, hlen, hpos, hpw⟩
      rw [List.pairwise_cons] at hpw
      rcases hpw with ⟨hhead, htail⟩
      have hd_ge : c ≤ d := hge d (by simp)
      have hd_pos : 0 < d := by omega
      have ht_part : IsPartition t.sum k t :=
        ⟨rfl, by simpa using hlen, fun a ha ↦ hpos a (by simp [ha]), htail⟩
      have ht_ge : ∀ a ∈ t, 2 * d ≤ a := by
        intro a ha
        rcases hhead a ha with ⟨hlt, hdvd⟩
        rcases hdvd with ⟨q, rfl⟩
        have hq2 : 2 ≤ q := by
          by_contra hlt2
          have : q ≤ 1 := by omega
          nlinarith
        nlinarith
      rcases ih (2 * d) t.sum t (by omega) ht_part ht_ge with ⟨ht_le, ht_uniq⟩
      have hident_d : d + 2 * d * (2 ^ k - 1) = d * (2 ^ (k + 1) - 1) := nat_geom_step d k
      have hn_eq : d + t.sum = n := by simpa [List.sum_cons] using hsum
      have hbound : c * (2 ^ (k + 1) - 1) ≤ n := by
        have h1 : c * (2 ^ (k + 1) - 1) ≤ d * (2 ^ (k + 1) - 1) :=
          Nat.mul_le_mul_right _ hd_ge
        omega
      refine ⟨hbound, fun heq ↦ ?_⟩
      have h2k1_pos : 1 ≤ 2 ^ (k + 1) - 1 := by
        have : 2 ≤ 2 ^ (k + 1) := by
          have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
          rw [pow_succ]; omega
        omega
      have hdc : d = c := by
        by_contra hne
        have hlt : c + 1 ≤ d := by omega
        have h1 : (c + 1) * (2 ^ (k + 1) - 1) ≤ d * (2 ^ (k + 1) - 1) :=
          Nat.mul_le_mul_right _ hlt
        nlinarith
      subst hdc
      have htsum : t.sum = (2 * d) * (2 ^ k - 1) := by omega
      have ht_eq : t = powTwoFrom (2 * d) k := ht_uniq htsum
      simp [powTwoFrom, ht_eq]

lemma part5 (k : ℕ) :
    (∀ n l, IsPartition n k l → 2 ^ k - 1 ≤ n) ∧ ∃! l, IsPartition (2 ^ k - 1) k l := by
  refine ⟨fun n l hl ↦ ?_, powTwoFrom 1 k, ?_, fun l hl ↦ ?_⟩
  · have h := (min_sum_and_unique_from k 1 n l (by omega) hl fun a ha ↦ by
      have := hl.2.2.1 a ha; omega).1
    simpa using h
  · simpa using (powTwoFrom_spec 1 k (by omega)).1
  · exact (min_sum_and_unique_from k 1 (2 ^ k - 1) l (by omega) hl fun a ha ↦ by
      have := hl.2.2.1 a ha; omega).2 (by simp)

end DivisibilityPartitions

theorem OMA.solution : type_of% @OMA.S_mo_315485.main :=
  ⟨fun n k l ↦ by
     simpa [DivisibilityPartitions.mem_partitions_iff 1 (by omega) k n l] using
       (⟨fun h ↦ h.1, fun h ↦ ⟨h, fun a ha ↦ by have := h.2.2.1 a ha; omega⟩⟩ :
         (IsPartition n k l ∧ ∀ a ∈ l, 1 ≤ a) ↔ IsPartition n k l),
   fun n k ↦ DivisibilityPartitions.card_partitions_eq_count 1 (by omega) k n,
   DivisibilityPartitions.exists_partition_of_cutoff,
   DivisibilityPartitions.exists_mul_many_partitions,
   DivisibilityPartitions.part5⟩
