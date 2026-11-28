import OMAStatements.S_mo_315485
import Mathlib

/-!
# Integer partitions under a divisibility constraint (MathOverflow 315485)

A sorted representative of a partition into k parts is a list l of positive integers with
sum n, length k and l_i < l_j and l_i | l_j whenever i < j.  The file proves all five claims
of the statement:

* `partitions lo k n` is exactly the set of such lists whose entries are all at least `lo`
  (so `partitions 1 k n` is the full solution set);
* its cardinality equals the recursive count `count lo k n`;
* every `n >= cutoff k` arises from a partition into `k+1` parts;
* multiples of a suitable `M` have at least `b` partitions into `k+2` parts;
* `2^k - 1` is the least sum of a `k`-part representative, and it has exactly one.

The counting bound uses the explicit modulus `M = product over j < b of (1 + 2*q*(2*q+1)^j)`
with `q = 2^(k+1) - 1`: each factor `E j` satisfies `E j - 1 = q * 2 * (2*q+1)^j`, so the
`b` divisors `n / E j` of `n` each give a different partition of `n` into `k+2` parts.

The existence bound splits `n = 2^a * m` with `m` odd.  If the two-part of `n` is large then
`n` is a multiple of `2^(2*k+2)`, which itself has the explicit `(k+2)`-part representative
`1, 2^(k+1)+1, 2*(2^(k+1)+1), ..., 2^k*(2^(k+1)+1)` (its sum is
`1 + (2^(k+1)+1)*(2^(k+1)-1) = 2^(2*k+2)`); otherwise `m >= 2*(2*cutoff k + 1)` is large and
a partition of `(m-1)/2` into `k+1` parts, after doubling, extends by the divisor `2^a`.
-/

open OMA.S_mo_315485

private lemma chain_lower_aux :
    ∀ (l : List ℕ) (c : ℕ), 1 ≤ c → l.Pairwise (fun a b => a < b ∧ a ∣ b) →
      (∀ b ∈ l, c ≤ b) → c * (2 ^ l.length - 1) ≤ l.sum := by
  intro l
  induction l with
  | nil => intro c hc _ _; simp
  | cons a t ih =>
      intro c hc hp hle
      rw [List.pairwise_cons] at hp
      obtain ⟨hhead, htail⟩ := hp
      have ha : c ≤ a := hle a (List.mem_cons_self ..)
      have ha1 : 1 ≤ a := le_trans hc ha
      have h2a : ∀ b ∈ t, 2 * a ≤ b := by
        intro b hb
        obtain ⟨hlt, hdvd⟩ := hhead b hb
        obtain ⟨k, hk⟩ := hdvd
        subst hk
        have hk2 : 2 ≤ k := by
          have h1 : a * 1 < a * k := by simpa using hlt
          have h2 : 1 < k := Nat.lt_of_mul_lt_mul_left (by simpa using h1)
          omega
        calc 2 * a = a * 2 := by ring
          _ ≤ a * k := Nat.mul_le_mul_left a hk2
      have hih : 2 * a * (2 ^ t.length - 1) ≤ t.sum := ih (2 * a) (by omega) htail h2a
      obtain ⟨K, hKdef⟩ : ∃ K, K = 2 ^ t.length - 1 := ⟨_, rfl⟩
      have hih2 : 2 * (a * K) ≤ t.sum := by rw [hKdef]; ring_nf; ring_nf at hih; exact hih
      have hK : 2 ^ (a :: t).length - 1 = 2 * K + 1 := by
        rw [hKdef]
        simp only [List.length_cons]
        have h2 : 2 ^ (t.length + 1) = 2 * 2 ^ t.length := by rw [pow_succ]; ring
        have hpos : 1 ≤ 2 ^ t.length := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hstep : c * (2 * K + 1) ≤ a * (2 * K + 1) := Nat.mul_le_mul_right _ ha
      have hexp : a * (2 * K + 1) = 2 * (a * K) + a := by ring
      rw [hK, List.sum_cons]
      calc c * (2 * K + 1) ≤ a * (2 * K + 1) := hstep
        _ = 2 * (a * K) + a := hexp
        _ ≤ t.sum + a := by omega
        _ = a + t.sum := by omega

private lemma chain_eq_aux :
    ∀ (l : List ℕ) (c : ℕ), 1 ≤ c → l.Pairwise (fun a b => a < b ∧ a ∣ b) →
      (∀ b ∈ l, c ≤ b) → l.sum = c * (2 ^ l.length - 1) →
      l = (List.range l.length).map (fun i => c * 2 ^ i) := by
  intro l
  induction l with
  | nil => intro c hc _ _ _; simp
  | cons a t ih =>
      intro c hc hp hle hsum
      rw [List.pairwise_cons] at hp
      obtain ⟨hhead, htail⟩ := hp
      have ha : c ≤ a := hle a (List.mem_cons_self ..)
      have ha1 : 1 ≤ a := le_trans hc ha
      have h2a : ∀ b ∈ t, 2 * a ≤ b := by
        intro b hb
        obtain ⟨hlt, hdvd⟩ := hhead b hb
        obtain ⟨k, hk⟩ := hdvd
        subst hk
        have hk2 : 2 ≤ k := by
          have h1 : a * 1 < a * k := by simpa using hlt
          have h2 : 1 < k := Nat.lt_of_mul_lt_mul_left (by simpa using h1)
          omega
        calc 2 * a = a * 2 := by ring
          _ ≤ a * k := Nat.mul_le_mul_left a hk2
      have hlb : 2 * a * (2 ^ t.length - 1) ≤ t.sum := chain_lower_aux t (2 * a) (by omega) htail h2a
      obtain ⟨K, hKdef⟩ : ∃ K, K = 2 ^ t.length - 1 := ⟨_, rfl⟩
      have hlb2 : 2 * (a * K) ≤ t.sum := by rw [hKdef]; ring_nf; ring_nf at hlb; exact hlb
      have hK : 2 ^ (a :: t).length - 1 = 2 * K + 1 := by
        rw [hKdef]
        simp only [List.length_cons]
        have h2 : 2 ^ (t.length + 1) = 2 * 2 ^ t.length := by rw [pow_succ]; ring
        have hpos : 1 ≤ 2 ^ t.length := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hsum' : a + t.sum = c * (2 * K + 1) := by
        have h := hsum
        rw [List.sum_cons] at h
        rw [hK] at h
        exact h
      have hKpos : 0 < 2 * K + 1 := by omega
      have hca : a ≤ c := by
        have h1 : a * (2 * K + 1) ≤ c * (2 * K + 1) := by
          have h2 : a * (2 * K + 1) = 2 * (a * K) + a := by ring
          omega
        exact Nat.le_of_mul_le_mul_right h1 hKpos
      have hce : c = a := le_antisymm ha hca
      have htsum : t.sum = 2 * (a * K) := by
        have hc1 : a * (2 * K + 1) = 2 * (a * K) + a := by ring
        rw [hce] at hsum'
        omega
      have hih := ih (2 * a) (by omega) htail h2a (by rw [htsum, hKdef]; ring)
      rw [hce, hih]
      simp only [List.length_cons, List.length_map, List.length_range, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp
      · apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply, pow_succ]
        ring

private lemma sum_map_mul' (d : ℕ) (m : List ℕ) :
    (m.map (fun x => d * x)).sum = d * m.sum := by
  rw [List.sum_map_mul_left]; simp

private lemma pairwise_map_mul {d : ℕ} (hd : 0 < d) (m : List ℕ) :
    List.Pairwise (fun a b => a < b ∧ a ∣ b) (m.map (fun x => d * x)) ↔
      List.Pairwise (fun a b => a < b ∧ a ∣ b) m := by
  rw [List.pairwise_map]
  constructor
  · intro h
    refine List.Pairwise.imp ?_ h
    intro a b hab
    obtain ⟨h1, h2⟩ := hab
    exact ⟨Nat.lt_of_mul_lt_mul_left h1, Nat.dvd_of_mul_dvd_mul_left hd h2⟩
  · intro h
    refine List.Pairwise.imp ?_ h
    intro a b hab
    obtain ⟨h1, h2⟩ := hab
    exact ⟨Nat.mul_lt_mul_of_pos_left h1 hd, Nat.mul_dvd_mul_left d h2⟩

private lemma mem_map_mul {d x : ℕ} {m : List ℕ} (hd : 0 < d) :
    d * x ∈ m.map (fun y => d * y) ↔ x ∈ m := by
  rw [List.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h : y = x := by
      have h2 : d * y / d = d * x / d := by rw [hxy]
      rwa [Nat.mul_div_right y hd, Nat.mul_div_right x hd] at h2
    rwa [h] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private lemma cons_map_div {d : ℕ} (hd : 0 < d) :
    ∀ (rest : List ℕ), (∀ a ∈ rest, d ∣ a) →
      ((rest.map (fun x => x / d)).map (fun x => d * x)) = rest
  | [], _ => rfl
  | a :: t, h => by
      have ha : d ∣ a := h a (by simp)
      have ht : ∀ b ∈ t, d ∣ b := fun b hb => h b (by simp [hb])
      simp only [List.map_cons]
      rw [cons_map_div hd t ht, Nat.mul_div_cancel' ha]

private lemma test_partitions_iff :
    ∀ (k : ℕ) (lo n : ℕ) (l : List ℕ),
      l ∈ partitions lo k n ↔ IsPartition n k l ∧ ∀ a ∈ l, lo ≤ a := by
  intro k
  induction k with
  | zero =>
      intro lo n l
      constructor
      · intro h
        by_cases hn : n = 0
        · rw [show partitions lo 0 n = (if n = 0 then {[]} else ∅) from rfl, if_pos hn] at h
          rw [Finset.mem_singleton] at h
          subst h
          subst hn
          refine ⟨?_, ?_⟩
          · simp [IsPartition]
          · simp
        · rw [show partitions lo 0 n = (if n = 0 then {[]} else ∅) from rfl, if_neg hn] at h
          exact absurd h (by simp)
      · rintro ⟨hI, hlo⟩
        rw [show partitions lo 0 n = (if n = 0 then {[]} else ∅) from rfl]
        have hlen : l.length = 0 := hI.2.1
        have hl : l = [] := List.eq_nil_of_length_eq_zero hlen
        have hn : n = 0 := by rw [← hI.1]; simp [hl]
        subst hl
        simp [hn]
  | succ k ih =>
      intro lo n l
      constructor
      · intro h
        rw [show partitions lo (k+1) n =
          ((n.divisors.filter (lo ≤ ·)).biUnion fun d => (partitions 2 k (n/d - 1)).image fun l => d :: l.map (d * ·)) from rfl] at h
        rw [Finset.mem_biUnion] at h
        obtain ⟨d, hd, hmem⟩ := h
        rw [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdvd, hnne⟩, hdlo⟩ := hd
        rw [Finset.mem_image] at hmem
        obtain ⟨m, hm, rfl⟩ := hmem
        obtain ⟨hI, h2⟩ := ih 2 (n/d - 1) m |>.mp hm
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hnne)
        have hnpos : 0 < n := Nat.pos_of_ne_zero hnne
        have hdle : d ≤ n := Nat.le_of_dvd hnpos hdvd
        have hmuldiv : d * (n/d) = n := Nat.mul_div_cancel' hdvd
        have hne : n/d ≠ 0 := by
          intro h0
          rw [h0, Nat.mul_zero] at hmuldiv
          omega
        have hge : 1 ≤ n/d := Nat.pos_of_ne_zero hne
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · -- sum
          show (d :: m.map (fun x => d * x)).sum = n
          rw [List.sum_cons, sum_map_mul', hI.1]
          have hcancel : d * (n/d) = n := Nat.mul_div_cancel' hdvd
          have hdecomp : n/d = (n/d - 1) + 1 := by omega
          rw [hdecomp, Nat.mul_add, Nat.mul_one] at hcancel
          omega
        · show (d :: m.map (fun x => d * x)).length = k + 1
          rw [List.length_cons, List.length_map, hI.2.1]
        · intro a ha
          rw [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hdpos
          · obtain ⟨x, hx, rfl⟩ := (List.mem_map).mp ha
            have hxpos : 0 < x := hI.2.2.1 x hx
            positivity
        · rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro b hb
            obtain ⟨x, hx, rfl⟩ := (List.mem_map).mp hb
            have hx2 : 2 ≤ x := h2 x hx
            exact ⟨by nlinarith, ⟨x, rfl⟩⟩
          · exact (pairwise_map_mul hdpos m).mpr hI.2.2.2
        · intro a ha
          rw [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hdlo
          · obtain ⟨x, hx, rfl⟩ := (List.mem_map).mp ha
            have hx2 : 2 ≤ x := h2 x hx
            calc lo ≤ d := hdlo
              _ ≤ d * x := by nlinarith
      · rintro ⟨hI, hlo⟩
        rw [show partitions lo (k+1) n =
          ((n.divisors.filter (lo ≤ ·)).biUnion fun d => (partitions 2 k (n/d - 1)).image fun l => d :: l.map (d * ·)) from rfl]
        match l, hI with
        | [], hI => exact absurd hI.2.1 (by simp)
        | d :: rest, hI =>
            have hsum : d + rest.sum = n := hI.1
            have hlen : rest.length = k := by simpa using hI.2.1
            have hpos : ∀ a ∈ d :: rest, 0 < a := hI.2.2.1
            have hpair : List.Pairwise (fun a b => a < b ∧ a ∣ b) (d :: rest) := hI.2.2.2
            rw [List.pairwise_cons] at hpair
            obtain ⟨hhead, htail⟩ := hpair
            have hdpos : 0 < d := hpos d (by simp)
            have hdvdrest : ∀ a ∈ rest, d ∣ a := fun a ha => (hhead a ha).2
            have hdvd : d ∣ n := by
              rw [← hsum]
              exact dvd_add (dvd_refl d) (List.dvd_sum hdvdrest)
            have hm : rest.map (fun x => x / d) ∈ partitions 2 k (n/d - 1) := by
              apply ih 2 (n/d - 1) (rest.map (fun x => x / d)) |>.mpr
              refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
              · -- sum
                have hident : rest = (rest.map (fun x => x / d)).map (fun x => d * x) := (cons_map_div hdpos rest hdvdrest).symm
                have hsumX : rest.sum = d * (rest.map (fun x => x / d)).sum := by
                  calc rest.sum = ((rest.map (fun x => x / d)).map (fun x => d * x)).sum := by
                        conv_lhs => rw [hident]
                    _ = d * (rest.map (fun x => x / d)).sum := sum_map_mul' d _
                have hnX : n = d * ((rest.map (fun x => x / d)).sum + 1) := by
                  rw [hsumX] at hsum
                  rw [← hsum]; ring
                rw [hnX, Nat.mul_div_right ((rest.map (fun x => x / d)).sum + 1) hdpos]
                omega
              · show (rest.map (fun x => x / d)).length = k
                rw [List.length_map, hlen]
              · intro a ha
                obtain ⟨x, hx, rfl⟩ := (List.mem_map).mp ha
                have hxpos : 0 < x := hpos x (by simp [hx])
                have hxd : d < x := (hhead x hx).1
                exact Nat.div_pos (by omega) (by omega)
              · have hident : rest = (rest.map (fun x => x / d)).map (fun x => d * x) := (cons_map_div hdpos rest hdvdrest).symm
                have hp : List.Pairwise (fun a b => a < b ∧ a ∣ b) ((rest.map (fun x => x / d)).map (fun x => d * x)) := by
                  rw [← hident]; exact htail
                exact (pairwise_map_mul hdpos _).mp hp
              · intro a ha
                obtain ⟨x, hx, rfl⟩ := (List.mem_map).mp ha
                have hxd : d < x := (hhead x hx).1
                obtain ⟨k, hk⟩ := hdvdrest x hx
                have hk2 : 2 ≤ k := by
                  have h1 : d * 1 < d * k := by rw [← hk]; simpa using hxd
                  have h2 : 1 < k := Nat.lt_of_mul_lt_mul_left h1
                  omega
                rw [hk, Nat.mul_div_right k hdpos]
                exact hk2
            -- assemble
            rw [Finset.mem_biUnion]
            refine ⟨d, ?_, ?_⟩
            · rw [Finset.mem_filter, Nat.mem_divisors]
              exact ⟨⟨hdvd, by omega⟩, hlo d (by simp)⟩
            · rw [Finset.mem_image]
              refine ⟨rest.map (fun x => x / d), hm, ?_⟩
              exact congrArg (List.cons d) (cons_map_div hdpos rest hdvdrest)

private lemma map_mul_injective {d : ℕ} (hd : 0 < d) :
    ∀ (m m' : List ℕ), m.map (fun x => d * x) = m'.map (fun x => d * x) → m = m'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: t, b :: u, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hab : a = b := Nat.mul_left_cancel hd h1
      rw [hab]
      rw [map_mul_injective hd t u h2]

private lemma cons_map_mul_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun m : List ℕ => d :: m.map (fun x => d * x)) := by
  intro m m' h
  simp only [List.cons.injEq] at h
  exact map_mul_injective hd m m' h.2

private lemma test_card_count :
    ∀ (k : ℕ) (lo n : ℕ), (partitions lo k n).card = count lo k n := by
  intro k
  induction k with
  | zero =>
      intro lo n
      by_cases hn : n = 0
      · rw [show partitions lo 0 n = (if n = 0 then {[]} else ∅) from rfl,
            show count lo 0 n = (if n = 0 then 1 else 0) from rfl, if_pos hn, if_pos hn]
        simp
      · rw [show partitions lo 0 n = (if n = 0 then {[]} else ∅) from rfl,
            show count lo 0 n = (if n = 0 then 1 else 0) from rfl, if_neg hn, if_neg hn]
        simp
  | succ k ih =>
      intro lo n
      rw [show partitions lo (k+1) n =
        ((n.divisors.filter (lo ≤ ·)).biUnion fun d => (partitions 2 k (n/d - 1)).image fun l => d :: l.map (d * ·)) from rfl]
      rw [show count lo (k+1) n = ∑ d ∈ n.divisors.filter (lo ≤ ·), count 2 k (n/d - 1) from rfl]
      rw [Finset.card_biUnion ?_]
      · refine Finset.sum_congr rfl ?_
        intro d hd
        rw [Finset.card_image_of_injective]
        · exact ih 2 (n/d - 1)
        · rw [Finset.mem_filter, Nat.mem_divisors] at hd
          obtain ⟨⟨hdvd, hnne⟩, hdlo⟩ := hd
          exact cons_map_mul_injective (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hnne))
      · intro d hd d' hd' hne
        show Disjoint (Finset.image (fun l => d :: List.map (fun x => d * x) l) (partitions 2 k (n / d - 1)))
          (Finset.image (fun l => d' :: List.map (fun x => d' * x) l) (partitions 2 k (n / d' - 1)))
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [Finset.mem_image] at hx hx'
        obtain ⟨m, hm, rfl⟩ := hx
        obtain ⟨m', hm', hEq⟩ := hx'
        simp only [List.cons.injEq] at hEq
        exact hne hEq.1.symm

private lemma geom_sum_range (k : ℕ) :
    ((List.range k).map (fun i => 2 ^ i)).sum = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.sum_range_succ, ih]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      omega

private lemma scaled_chain_isPartition (k u : ℕ) (hu : 0 < u) :
    IsPartition (u * (2 ^ (k+1) - 1)) (k+1) ((List.range (k+1)).map (fun i => u * 2 ^ i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.sum_map_mul_left, geom_sum_range]
  · rw [List.length_map, List.length_range]
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have h1 : 0 < 2 ^ i := Nat.pow_pos (by norm_num : (0:ℕ) < 2)
    positivity
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro i j hij
    exact ⟨Nat.mul_lt_mul_of_pos_left ((Nat.pow_lt_pow_iff_right (by norm_num)).mpr hij) hu,
      Nat.mul_dvd_mul_left u (Nat.pow_dvd_pow 2 (le_of_lt hij))⟩

private lemma test_conj4 (k b : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → M ∣ n → b ≤ count 1 (k+2) n := by
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = 2 ^ (k+1) - 1 := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    have h : 2 ≤ 2 ^ (k+1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E, hEval⟩ : ∃ E : ℕ → ℕ, ∀ j, E j = 1 + 2*q*(2*q+1)^j := ⟨_, fun j => rfl⟩
  have hE_ge3 : ∀ j, 3 ≤ E j := by
    intro j
    rw [hEval]
    have h2q : 2 ≤ 2*q := by omega
    have hp : 1 ≤ (2*q+1)^j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hE_pos : ∀ j, 0 < E j := fun j => by have := hE_ge3 j; omega
  have hE_dvd : ∀ j, q ∣ E j - 1 := by
    intro j
    rw [hEval]
    have h1 : 1 + 2*q*(2*q+1)^j - 1 = 2*q*(2*q+1)^j := by omega
    rw [h1]
    exact ⟨2*(2*q+1)^j, by ring⟩
  have hE_lt : ∀ j, E j < E (j+1) := by
    intro j
    rw [hEval, hEval]
    have hbase : 1 < 2*q+1 := by omega
    have hp : (2*q+1)^j < (2*q+1)^(j+1) := (Nat.pow_lt_pow_iff_right hbase).mpr (by omega)
    have h2q : 0 < 2*q := by omega
    nlinarith
  have hE_inj : Function.Injective E := (strictMono_nat_of_lt_succ hE_lt).injective
  refine ⟨∏ j ∈ Finset.range b, E j, ?_, ?_⟩
  · exact Finset.prod_pos (fun j _ => hE_pos j)
  · intro n hnpos hMn
    have hEjn : ∀ j ∈ Finset.range b, E j ∣ n := by
      intro j hj
      exact dvd_trans (Finset.dvd_prod_of_mem E hj) hMn
    have huq : ∀ j, q * ((E j - 1)/q) = E j - 1 := fun j => Nat.mul_div_cancel' (hE_dvd j)
    have hu_ge2 : ∀ j, 2 ≤ (E j - 1)/q := by
      intro j
      have h := huq j
      have hqpos : 0 < q := by omega
      have h1 : 2*q ≤ q * ((E j - 1)/q) := by
        rw [h, hEval]
        have h2 : 2*q*1 ≤ 2*q*(2*q+1)^j := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
        omega
      have h1' : q * 2 ≤ q * ((E j - 1)/q) := by rw [mul_comm q 2]; exact h1
      exact Nat.le_of_mul_le_mul_left h1' hqpos
    have hI : ∀ j, IsPartition (E j - 1) (k+1) ((List.range (k+1)).map (fun i => ((E j - 1)/q) * 2 ^ i)) := by
      intro j
      have hu : 0 < (E j - 1)/q := by have := hu_ge2 j; omega
      have h := scaled_chain_isPartition k ((E j - 1)/q) hu
      have heq : (E j - 1)/q * (2 ^ (k+1) - 1) = E j - 1 := by
        rw [← hqdef, mul_comm]
        exact huq j
      rwa [heq] at h
    have hmem : ∀ j, (List.range (k+1)).map (fun i => ((E j - 1)/q) * 2 ^ i) ∈ partitions 2 (k+1) (E j - 1) := by
      intro j
      refine (test_partitions_iff (k+1) 2 (E j - 1) _).mpr ⟨hI j, ?_⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      have h1 : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num : 0 < 2)
      have h2 := hu_ge2 j
      nlinarith
    have hcount : ∀ j, 1 ≤ count 2 (k+1) (E j - 1) := by
      intro j
      rw [← test_card_count (k+1) 2 (E j - 1)]
      exact Finset.card_pos.mpr ⟨_, hmem j⟩
    obtain ⟨D, hDdef⟩ : ∃ D : Finset ℕ, D = (Finset.range b).image (fun j => n / E j) := ⟨_, rfl⟩
    have hinj : Set.InjOn (fun j => n / E j) ↑(Finset.range b) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have hEi : E i ∣ n := hEjn i (Finset.mem_range.mpr hi)
      have hEj : E j ∣ n := hEjn j (Finset.mem_range.mpr hj)
      have hdpos : 0 < n / E i := Nat.div_pos (Nat.le_of_dvd hnpos hEi) (hE_pos i)
      have h1 : E i * (n / E i) = E j * (n / E j) := by
        rw [Nat.mul_div_cancel' hEi, Nat.mul_div_cancel' hEj]
      rw [show n / E i = n / E j from hij] at h1
      have hdj : 0 < n / E j := Nat.div_pos (Nat.le_of_dvd hnpos hEj) (hE_pos j)
      exact hE_inj (Nat.mul_right_cancel hdj h1)
    have hDcard : D.card = b := by
      rw [hDdef, Finset.card_image_iff.mpr hinj, Finset.card_range]
    have hDsub : D ⊆ n.divisors.filter (1 ≤ ·) := by
      intro d hd
      rw [hDdef] at hd
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
      have hEj : E j ∣ n := hEjn j hj
      have hdvd : n / E j ∣ n := Nat.div_dvd_of_dvd hEj
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hdvd, by omega⟩, Nat.div_pos (Nat.le_of_dvd hnpos hEj) (hE_pos j)⟩
    have hstep1 : b = ∑ d ∈ D, (1:ℕ) := by
      rw [Finset.sum_const, hDcard]
      simp
    have hstep2 : ∑ d ∈ D, (1:ℕ) ≤ ∑ d ∈ D, count 2 (k+1) (n/d - 1) := by
      refine Finset.sum_le_sum ?_
      intro d hd
      rw [hDdef] at hd
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
      have hEj : E j ∣ n := hEjn j hj
      have hdpos : 0 < n / E j := Nat.div_pos (Nat.le_of_dvd hnpos hEj) (hE_pos j)
      have hdiv : n / (n / E j) = E j := by
        obtain ⟨d, hd⟩ : ∃ d, n / E j = d := ⟨_, rfl⟩
        have hdpos' : 0 < d := by rw [← hd]; exact hdpos
        have hn_eq : n = d * E j := by
          rw [← hd, mul_comm, Nat.mul_div_cancel' hEj]
        rw [hd, hn_eq, Nat.mul_div_right (E j) hdpos']
      rw [hdiv]
      exact hcount j
    have hstep3 : ∑ d ∈ D, count 2 (k+1) (n/d - 1) ≤
        ∑ d ∈ n.divisors.filter (1 ≤ ·), count 2 (k+1) (n/d - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hDsub (by intro i _ _; exact Nat.zero_le _)
    have hfinal : count 1 (k+2) n = ∑ d ∈ n.divisors.filter (1 ≤ ·), count 2 (k+1) (n/d - 1) := rfl
    calc b = ∑ d ∈ D, (1:ℕ) := hstep1
      _ ≤ ∑ d ∈ D, count 2 (k+1) (n/d - 1) := hstep2
      _ ≤ ∑ d ∈ n.divisors.filter (1 ≤ ·), count 2 (k+1) (n/d - 1) := hstep3
      _ = count 1 (k+2) n := hfinal.symm

private lemma conj5 (k : ℕ) :
    (∀ n l, IsPartition n k l → 2 ^ k - 1 ≤ n) ∧ ∃! l, IsPartition (2 ^ k - 1) k l := by
  constructor
  · intro n l h
    have hp : l.Pairwise (fun a b => a < b ∧ a ∣ b) := h.2.2.2
    have hpos : ∀ b ∈ l, 0 < b := h.2.2.1
    have hle : ∀ b ∈ l, 1 ≤ b := fun b hb => hpos b hb
    have h1 := chain_lower_aux l 1 le_rfl hp hle
    rw [Nat.one_mul, h.1, h.2.1] at h1
    exact h1
  · refine ⟨(List.range k).map (fun i => 2 ^ i), ?_, ?_⟩
    · refine ⟨geom_sum_range k, ?_, ?_, ?_⟩
      · simp
      · intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        positivity
      · rw [List.pairwise_map]
        refine List.Pairwise.imp ?_ List.pairwise_lt_range
        intro i j hij
        exact ⟨(Nat.pow_lt_pow_iff_right (by norm_num)).mpr hij, Nat.pow_dvd_pow 2 (le_of_lt hij)⟩
    · intro l hl
      have hp : l.Pairwise (fun a b => a < b ∧ a ∣ b) := hl.2.2.2
      have hpos : ∀ b ∈ l, 0 < b := hl.2.2.1
      have hle : ∀ b ∈ l, 1 ≤ b := fun b hb => hpos b hb
      have hsum : l.sum = 1 * (2 ^ l.length - 1) := by
        rw [hl.1, hl.2.1, Nat.one_mul]
      have h := chain_eq_aux l 1 le_rfl hp hle hsum
      rw [hl.2.1] at h
      simpa using h

private lemma exists_odd_part : ∀ n : ℕ, 0 < n → ∃ a m : ℕ, n = 2^a * m ∧ Odd m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
    · have hkpos : 0 < k := by omega
      obtain ⟨a, m, hm, hodd⟩ := ih k (by omega) hkpos
      exact ⟨a+1, m, by rw [hk, hm, pow_succ']; ring, hodd⟩
    · exact ⟨0, n, by simp, hodd⟩

private lemma isPartition_scale {j t : ℕ} (ht : 0 < t) {x : ℕ} {l : List ℕ}
    (hl : IsPartition x j l) : IsPartition (t*x) j (l.map (fun a => t * a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (l.map (fun a => t * a)).sum = t * x
    rw [sum_map_mul', hl.1]
  · rw [List.length_map, hl.2.1]
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hbpos : 0 < b := hl.2.2.1 b hb
    positivity
  · exact (pairwise_map_mul ht l).mpr hl.2.2.2

private lemma chain_of_strict_dvd (j : ℕ) {n d : ℕ} (hdvd : d ∣ n) (hn : 0 < n) (hd : 0 < d)
    (h : ∃ m : List ℕ, IsPartition (n/d - 1) j m ∧ ∀ a ∈ m, 2 ≤ a) :
    ∃ l : List ℕ, IsPartition n (j+1) l := by
  obtain ⟨m, hI, h2⟩ := h
  have hmem : m ∈ partitions 2 j (n/d - 1) := (test_partitions_iff j 2 (n/d - 1) m).mpr ⟨hI, h2⟩
  have hdmem : d ∈ n.divisors.filter (1 ≤ ·) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, by omega⟩, by omega⟩
  refine ⟨d :: m.map (fun a => d * a), ?_⟩
  have hrec : d :: m.map (fun a => d * a) ∈ partitions 1 (j+1) n := by
    rw [show partitions 1 (j+1) n = ((n.divisors.filter (1 ≤ ·)).biUnion fun d =>
      (partitions 2 j (n/d - 1)).image fun l => d :: l.map (d * ·)) from rfl]
    rw [Finset.mem_biUnion]
    exact ⟨d, hdmem, Finset.mem_image.mpr ⟨m, hmem, rfl⟩⟩
  exact ((test_partitions_iff (j+1) 1 n _).mp hrec).1

private lemma core_chain (j : ℕ) :
    ∃ l : List ℕ, IsPartition (2^(2*j+2)) (j+2) l := by
  obtain ⟨u, hu⟩ : ∃ u, 2^(j+1) = u + 1 := ⟨2^(j+1) - 1, by
    have h : 1 ≤ 2^(j+1) := Nat.one_le_pow _ _ (by norm_num)
    omega⟩
  refine ⟨1 :: (List.range (j+1)).map (fun i => (2^(j+1)+1) * 2^i), ?_⟩
  have hmain : (2^(j+1) + 1) * (2^(j+1) - 1) = 2^(2*j+2) - 1 := by
    have h1 : 1 ≤ 2^(j+1) := Nat.one_le_pow _ _ (by norm_num)
    have hR : 1 ≤ 2^(2*j+2) := Nat.one_le_pow _ _ (by norm_num)
    have hpow : 2^(2*j+2) = 2^(j+1) * 2^(j+1) := by
      rw [show 2*j+2 = (j+1)*2 from by ring, pow_mul, pow_two]
    have harith : (2^(j+1) + 1) * (2^(j+1) - 1) + 1 = 2^(j+1) * 2^(j+1) := by
      zify [h1]
      ring
    omega
  have hsum : ((List.range (j+1)).map (fun i => (2^(j+1)+1) * 2^i)).sum
      = 2^(2*j+2) - 1 := by
    rw [List.sum_map_mul_left, geom_sum_range, hmain]
  have hq3 : 3 ≤ 2^(j+1) + 1 := by
    have h : 2 ≤ 2^(j+1) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(j+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hR2 : 1 ≤ 2^(2*j+2) := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (1 :: (List.range (j+1)).map (fun i => (2^(j+1)+1) * 2^i)).sum = 2^(2*j+2)
    rw [List.sum_cons, hsum]
    omega
  · show (1 :: (List.range (j+1)).map (fun i => (2^(j+1)+1) * 2^i)).length = j+2
    simp
  · intro a ha
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · norm_num
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      have h1 : 0 < 2^i := Nat.pow_pos (by norm_num : (0:ℕ) < 2)
      positivity
  · rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have h1i : 1 ≤ 2^i := Nat.one_le_pow _ _ (by norm_num)
      refine ⟨?_, one_dvd _⟩
      calc 1 < 3 := by norm_num
        _ = 3 * 1 := by ring
        _ ≤ (2^(j+1)+1) * 2^i := Nat.mul_le_mul hq3 h1i
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ List.pairwise_lt_range
      intro i k hik
      exact ⟨Nat.mul_lt_mul_of_pos_left ((Nat.pow_lt_pow_iff_right (by norm_num)).mpr hik)
          (by omega : 0 < 2^(j+1)+1),
        Nat.mul_dvd_mul_left (2^(j+1)+1) (Nat.pow_dvd_pow 2 (le_of_lt hik))⟩

private lemma conj3 : ∀ (n k : ℕ), cutoff k ≤ n → ∃ l : List ℕ, IsPartition n (k+1) l := by
  intro n k
  induction k generalizing n with
  | zero =>
      intro hn
      refine ⟨[n], ?_⟩
      have hc : cutoff 0 = 1 := rfl
      refine ⟨by simp, by simp, ?_, by simp⟩
      intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      omega
  | succ k ih =>
      intro hn
      have hc1 : 0 < cutoff (k+1) := by
        rw [show cutoff (k+1) = 2^(2*k+2) * (2*cutoff k + 1) from rfl]
        positivity
      obtain ⟨a, m, hnm, hodd⟩ := exists_odd_part n (by omega)
      rcases Nat.lt_or_ge a (2*k+2) with ha | ha
      · -- Case B: the odd part m is large
        have hm : 2*(2*cutoff k + 1) ≤ m := by
          have h2a : 2^a ≤ 2^(2*k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2apos : 0 < 2^(2*k+1) := Nat.pow_pos (by norm_num : (0:ℕ) < 2)
          have hcut : cutoff (k+1) ≤ n := hn
          have h1 : 2^(2*k+1) * (2*(2*cutoff k + 1)) ≤ 2^(2*k+1) * m := by
            calc 2^(2*k+1) * (2*(2*cutoff k + 1))
                = 2^(2*k+2) * (2*cutoff k + 1) := by
                  rw [show 2*k+2 = 2*k+1+1 from by ring, pow_succ]
                  ring
              _ ≤ n := hcut
              _ = 2^a * m := hnm
              _ ≤ 2^(2*k+1) * m := Nat.mul_le_mul_right m h2a
          exact Nat.le_of_mul_le_mul_left h1 h2apos
        rcases hodd with ⟨x, hx⟩
        have hxge : cutoff k ≤ x := by
          have h1 : 4*cutoff k + 2 ≤ 2*x + 1 := by
            calc 4*cutoff k + 2 = 2*(2*cutoff k+1) := by ring
              _ ≤ m := hm
              _ = 2*x+1 := hx
          omega
        obtain ⟨l, hl⟩ := ih x hxge
        have hstrict : ∃ l' : List ℕ, IsPartition (m - 1) (k+1) l' ∧ ∀ b ∈ l', 2 ≤ b := by
          refine ⟨l.map (fun b => 2*b), ?_, ?_⟩
          · have hscale := isPartition_scale (j := k+1) (t := 2) (by norm_num) (x := x) hl
            have h2x : 2 * x = m - 1 := by rw [hx]; omega
            rwa [h2x] at hscale
          · intro b hb
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
            have hc0 : 0 < c := hl.2.2.1 c hc
            omega
        obtain ⟨l', hl', h2'⟩ := hstrict
        have hdiv : n / 2^a = m := by
          rw [hnm]
          exact Nat.mul_div_right m (Nat.pow_pos (by norm_num : (0:ℕ) < 2))
        have hdvd : 2^a ∣ n := by
          rw [hnm]
          exact dvd_mul_right _ _
        obtain ⟨l'', hl''⟩ := chain_of_strict_dvd (k+1) hdvd (by omega)
          (Nat.pow_pos (by norm_num : (0:ℕ) < 2)) ⟨l', by rw [hdiv]; exact hl', h2'⟩
        exact ⟨l'', hl''⟩
      · -- Case A: n is divisible by 2^(2k+2)
        obtain ⟨t, ht⟩ : ∃ t, n = 2^(2*k+2) * t := by
          refine ⟨2^(a - (2*k+2)) * m, ?_⟩
          have hexp : 2^a = 2^(2*k+2) * 2^(a - (2*k+2)) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hnm, hexp]
          ring
        have htpos : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · rw [ht, h0, mul_zero] at hn
            omega
          · exact h0
        obtain ⟨l, hl⟩ := core_chain k
        have hscale := isPartition_scale (j := k+2) (t := t) htpos (x := 2^(2*k+2)) hl
        exact ⟨l.map (fun b => t*b), by rw [ht, mul_comm]; exact hscale⟩

theorem OMA.solution : type_of% @OMA.S_mo_315485.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n k l
    constructor
    · intro h
      exact ((test_partitions_iff k 1 n l).mp h).1
    · intro h
      exact (test_partitions_iff k 1 n l).mpr ⟨h, fun a ha => h.2.2.1 a ha⟩
  · intro n k
    exact test_card_count k 1 n
  · exact conj3
  · exact test_conj4
  · exact conj5
