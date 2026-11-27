import FormalConjectures.ErdosProblems.«124»

/-!
# Completeness of the positive powers of 3, 4 and 7

Burr, Erdős, Graham and Li established this case in *Complete sequences of
sets of integer powers*, Acta Arithmetica 77 (1996), 133–138. Here a finite
subset-sum calculation gives the interval from 582 through 4460. Adding the
least unused power repeatedly extends this interval. The required gap bound
follows from the periodic residues of powers of 3 and 4 modulo 248139202560.
-/

-- Credit: @MrSeizy

namespace OMA.Powers347

def Bounded (d e n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ i ∈ s, i < e) ∧ (∑ i ∈ s, d ^ (i+1)) = n

def Rep (a b c n : ℕ) : Prop :=
  ∃ x y z : ℕ, Bounded 3 a x ∧ Bounded 4 b y ∧ Bounded 7 c z ∧ x+y+z=n

private def addPowers (d bits : ℕ) : ℕ → ℕ
  | 0 => bits
  | e+1 =>
    let old := addPowers d bits e
    old ||| (old <<< (d^(e+1)))

private lemma addPowers_sound {d bits e n : ℕ} (h : (addPowers d bits e).testBit n = true) :
    ∃ t u : ℕ, bits.testBit t = true ∧ Bounded d e u ∧ t + u = n := by
  induction e generalizing n with
  | zero =>
    exact ⟨n, 0, h, ⟨∅, by simp, by simp⟩, Nat.add_zero n⟩
  | succ e ih =>
    simp only [addPowers, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with old | ⟨hle, added⟩
    · obtain ⟨t, u, ht, ⟨s, hs, hsum⟩, htu⟩ := ih old
      exact ⟨t, u, ht, ⟨s, fun i hi => (hs i hi).trans (Nat.lt_succ_self e), hsum⟩, htu⟩
    · obtain ⟨t, u, ht, ⟨s, hs, hsum⟩, htu⟩ := ih added
      have fresh : e ∉ s := fun he => (Nat.lt_irrefl e) (hs e he)
      refine ⟨t, d^(e+1) + u, ht, ⟨insert e s, ?_, ?_⟩, by omega⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Nat.lt_succ_self _
        · exact (hs i hi).trans (Nat.lt_succ_self _)
      · rw [Finset.sum_insert fresh, hsum]

private def seedBits := addPowers 7 (addPowers 4 (addPowers 3 1 7) 5) 3

private def intervalBits : ℕ := (2 ^ 3879 - 1) <<< 582

private lemma seed_checked : seedBits &&& intervalBits = intervalBits := by decide +kernel

private lemma interval_bit (width start n : ℕ) (hl : start ≤ n) (hu : n-start < width) :
    (((2^width - 1) <<< start : ℕ).testBit n) = true := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true hl, decide_eq_true hu]
  rfl

lemma seed (n : ℕ) (hn : 582 ≤ n) (h : n ≤ 4460) : Rep 7 5 3 n := by
  have inRange : intervalBits.testBit n = true := interval_bit 3879 582 n hn (by omega)
  have included := congrArg (fun m : ℕ => m.testBit n) seed_checked
  have bit : seedBits.testBit n = true := by
    simpa only [Nat.testBit_and, inRange, Bool.and_true] using included
  obtain ⟨s, z, hs, hz, hsz⟩ := addPowers_sound (e := 3) (d := 7) (bits := addPowers 4 (addPowers 3 1 7) 5) bit
  obtain ⟨r, y, hr, hy, hry⟩ := addPowers_sound (e := 5) (d := 4) (bits := addPowers 3 1 7) hs
  obtain ⟨t, x, ht, hx, htx⟩ := addPowers_sound (e := 7) (d := 3) (bits := 1) hr
  have : t = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht
  exact ⟨x, y, z, hx, hy, hz, by omega⟩

private def mass (a b c : ℕ) : ℕ :=
  3 * 3^(a+1) + 2 * 4^(b+1) + 7^(c+1)

private def Cover (a b c : ℕ) : Prop :=
  ∀ n, 582 ≤ n → 6*n + 3516 ≤ mass a b c → Rep a b c n

private lemma widen {d e f x : ℕ} (h : Bounded d e x) (hef : e ≤ f) : Bounded d f x := by
  obtain ⟨s, hs, hx⟩ := h
  exact ⟨s, fun i hi => (hs i hi).trans_le hef, hx⟩

private lemma addNext {d e x : ℕ} (h : Bounded d e x) : Bounded d (e+1) (x+d^(e+1)) := by
  obtain ⟨s, hs, hx⟩ := h
  have he : e ∉ s := fun h => (Nat.lt_irrefl e) (hs e h)
  refine ⟨insert e s, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Nat.lt_succ_self _
    · exact (hs i hi).trans (Nat.lt_succ_self _)
  · rw [Finset.sum_insert he, hx, Nat.add_comm]

private lemma rep_widen {a b c a' b' c' n : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (h : Rep a b c n) : Rep a' b' c' n := by
  obtain ⟨x,y,z,hx,hy,hz,hxyz⟩ := h
  exact ⟨x,y,z,widen hx ha,widen hy hb,widen hz hc,hxyz⟩

private lemma extend_interval {M w : ℕ} {P Q : ℕ → Prop}
    (cover : ∀ n, 582 ≤ n → 6*n + 3516 ≤ M → P n)
    (overlap : 6*w + 7002 ≤ M)
    (keep : ∀ n, P n → Q n) (add : ∀ n, P n → Q (n+w)) :
    ∀ n, 582 ≤ n → 6*n + 3516 ≤ M+6*w → Q n := by
  intro n hn hmass
  by_cases old : 6*n + 3516 ≤ M
  · exact keep n (cover n hn old)
  · have hlow : 582 ≤ n-w := by omega
    have hsub : 6*(n-w) + 3516 ≤ M := by omega
    have done := add _ (cover _ hlow hsub)
    rwa [Nat.sub_add_cancel (by omega : w ≤ n)] at done

private lemma next_interval (a b c : ℕ) (covered : Cover a b c)
    (gap : 6*min (3^(a+1)) (min (4^(b+1)) (7^(c+1))) + 7002 ≤ mass a b c) :
    ∃ a' b' c', a ≤ a' ∧ b ≤ b' ∧ c ≤ c' ∧ mass a b c < mass a' b' c' ∧ Cover a' b' c' := by
  let u := 3^(a+1)
  let v := 4^(b+1)
  let w := 7^(c+1)
  change 6*min u (min v w) + 7002 ≤ mass a b c at gap
  by_cases hu : u ≤ min v w
  · rw [min_eq_left hu] at gap
    have inc : mass (a+1) b c = mass a b c + 6*u := by dsimp [mass,u]; ring
    refine ⟨a+1,b,c,by omega,le_rfl,le_rfl,?_,?_⟩
    · rw [inc]
      have : 0 < u := by dsimp [u]; positivity
      omega
    · unfold Cover
      rw [inc]
      apply extend_interval covered gap (fun _ => rep_widen (by omega) le_rfl le_rfl)
      rintro n ⟨x,y,z,hx,hy,hz,hxyz⟩
      exact ⟨x+u,y,z,addNext hx,hy,hz,by omega⟩
  · rw [min_eq_right (by omega : min v w ≤ u)] at gap
    by_cases hv : v ≤ w
    · rw [min_eq_left hv] at gap
      have inc : mass a (b+1) c = mass a b c + 6*v := by dsimp [mass,v]; ring
      refine ⟨a,b+1,c,le_rfl,by omega,le_rfl,?_,?_⟩
      · rw [inc]
        have : 0 < v := by dsimp [v]; positivity
        omega
      · unfold Cover
        rw [inc]
        apply extend_interval covered gap (fun _ => rep_widen le_rfl (by omega) le_rfl)
        rintro n ⟨x,y,z,hx,hy,hz,hxyz⟩
        exact ⟨x,y+v,z,hx,addNext hy,hz,by omega⟩
    · rw [min_eq_right (by omega : w ≤ v)] at gap
      have inc : mass a b (c+1) = mass a b c + 6*w := by dsimp [mass,w]; ring
      refine ⟨a,b,c+1,le_rfl,le_rfl,by omega,?_,?_⟩
      · rw [inc]
        have : 0 < w := by dsimp [w]; positivity
        omega
      · unfold Cover
        rw [inc]
        apply extend_interval covered gap (fun _ => rep_widen le_rfl le_rfl (by omega))
        rintro n ⟨x,y,z,hx,hy,hz,hxyz⟩
        exact ⟨x,y,z+w,hx,hy,addNext hz,by omega⟩

private lemma to_distinct_powers {d e n : ℕ} (h : Bounded d e n) :
    n ∈ Erdos124.sumsOfDistinctPowers d 1 := by
  obtain ⟨s, _, hs⟩ := h
  let shift : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  refine ⟨s.map shift, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact Nat.succ_le_succ (Nat.zero_le j)
  · rw [Finset.sum_map]
    exact hs

open scoped Pointwise in
lemma eventually_of_gap (gap : ∀ a b c : ℕ, 7 ≤ a → 5 ≤ b → 3 ≤ c →
    let u := 3^(a+1)
    let v := 4^(b+1)
    let w := 7^(c+1)
    6 * min u (min v w) + 7002 ≤ 3*u + 2*v + w) :
    ∀ᶠ n in Filter.atTop, n ∈ Erdos124.sumsOfDistinctPowers 3 1 +
      Erdos124.sumsOfDistinctPowers 4 1 + Erdos124.sumsOfDistinctPowers 7 1 := by
  have reach (t : ℕ) : ∃ a b c, 7 ≤ a ∧ 5 ≤ b ∧ 3 ≤ c ∧ t ≤ mass a b c ∧ Cover a b c := by
    induction t with
    | zero =>
      refine ⟨7,5,3,le_rfl,le_rfl,le_rfl,Nat.zero_le _,?_⟩
      intro n hn hmass
      have hbase : mass 7 5 3 = 30276 := by decide
      rw [hbase] at hmass
      exact seed n hn (by omega)
    | succ t ih =>
      obtain ⟨a,b,c,ha,hb,hc,ht,hcover⟩ := ih
      obtain ⟨a',b',c',ha',hb',hc',hgt,hnext⟩ := next_interval a b c hcover (gap a b c ha hb hc)
      exact ⟨a',b',c',ha.trans ha',hb.trans hb',hc.trans hc',by omega,hnext⟩
  apply Filter.eventually_atTop.2
  refine ⟨582, ?_⟩
  intro n hn
  obtain ⟨a,b,c,_,_,_,hbound,hcover⟩ := reach (6*n+3516)
  obtain ⟨x,y,z,hx,hy,hz,hxyz⟩ := hcover n hn hbound
  exact ⟨x+y, ⟨x,to_distinct_powers hx,y,to_distinct_powers hy,rfl⟩,
    z,to_distinct_powers hz,hxyz⟩

end OMA.Powers347

namespace OMA.Powers347

private def modulus : ℕ := 248139202560

private inductive PivotTree
  | nil
  | node (pivot : ℕ) (left right : PivotTree)

private def containsResidue : PivotTree → ℕ → Bool
  | .nil, _ => false
  | .node p l r, x =>
    if x < p then containsResidue l x else if p < x then containsResidue r x else true

private def separated : PivotTree → ℕ → Bool
  | .nil, _ => true
  | .node p l r, u =>
    if u + 3501 ≤ p then separated l u
    else if p + 2334 ≤ u then separated r u else false

private lemma separated_sound (tree : PivotTree) (u v : ℕ)
    (hu : separated tree u = true) (hv : containsResidue tree v = true) :
    u+3501 ≤ v ∨ v+2334 ≤ u := by
  induction tree with
  | nil => simp [containsResidue] at hv
  | node pivot l r hl hr =>
    by_cases h : u + 3501 ≤ pivot
    · by_cases smaller : v < pivot
      · exact hl (by simpa [separated, h] using hu)
          (by simpa [containsResidue, smaller] using hv)
      · omega
    · by_cases h' : pivot + 2334 ≤ u
      · by_cases larger : pivot < v
        · exact hr (by simpa [separated, h, h'] using hu)
            (by simpa [containsResidue, Nat.not_lt_of_ge larger.le, larger] using hv)
        · omega
      · simp [separated, h, h'] at hu

/-- The 116 residues of powers of four from exponent seven onward. -/
private def landmarks : PivotTree :=
 (.node 79418343424
    (.node 29997481984
      (.node 6059032576
        (.node 268435456
          (.node 1048576 (.node 65536 (.node 16384 .nil .nil) (.node 262144 .nil .nil)) (.node 16777216 (.node 4194304 .nil .nil) (.node 67108864 .nil .nil)))
          (.node 3752820736 (.node 1073741824 (.node 969293824 .nil .nil) (.node 3087745024 .nil .nil)) (.node 4294967296 (.node 3877175296 .nil .nil) .nil)))
        (.node 17179869184
          (.node 12350980096 (.node 8849096704 (.node 6346522624 .nil .nil) (.node 11100798976 .nil .nil)) (.node 15508701184 (.node 15011282944 .nil .nil) (.node 15905357824 .nil .nil)))
          (.node 24236130304 (.node 18073944064 (.node 17576525824 .nil .nil) (.node 20067598336 .nil .nil)) (.node 26738704384 (.node 25386090496 .nil .nil) .nil))))
      (.node 49403920384
        (.node 38910017536
          (.node 33081032704 (.node 32115933184 (.node 32011485184 .nil .nil) (.node 33018118144 .nil .nil)) (.node 33085210624 (.node 33084964864 .nil .nil) (.node 35396386816 .nil .nil)))
          (.node 44403195904 (.node 41043902464 (.node 40780939264 .nil .nil) (.node 43630280704 .nil .nil)) (.node 47219900416 (.node 46045118464 .nil .nil) .nil)))
        (.node 67051700224
          (.node 62277124096 (.node 60045131776 (.node 59398537216 .nil .nil) (.node 62034804736 .nil .nil)) (.node 63621431296 (.node 62806736896 .nil .nil) .nil))
          (.node 70306103296 (.node 69534171136 (.node 68719476736 .nil .nil) (.node 70063783936 .nil .nil)) (.node 72942370816 (.node 72295776256 .nil .nil) .nil)))))
    (.node 156216623104
      (.node 126281875456
        (.node 106954817536
          (.node 92344827904 (.node 85121007616 (.node 80270393344 .nil .nil) (.node 85392523264 .nil .nil)) (.node 96944521216 (.node 93430890496 .nil .nil) (.node 101544361984 .nil .nil)))
          (.node 121240109056 (.node 119989927936 (.node 112273309696 .nil .nil) (.node 120800395264 .nil .nil)) (.node 125584359424 (.node 125007806464 .nil .nil) .nil)))
        (.node 132340842496
          (.node 132072472576 (.node 128463732736 (.node 128045940736 .nil .nil) (.node 128588087296 .nil .nil)) (.node 132339859456 (.node 132324130816 .nil .nil) .nil))
          (.node 145349853184 (.node 139638882304 (.node 135874576384 .nil .nil) (.node 141585547264 .nil .nil)) (.node 155640070144 (.node 145417732096 .nil .nil) .nil))))
      (.node 201806086144
        (.node 182864429056
          (.node 164175609856 (.node 160424034304 (.node 158038245376 .nil .nil) (.node 163123757056 .nil .nil)) (.node 177612783616 (.node 174521122816 .nil .nil) (.node 179680067584 .nil .nil)))
          (.node 196299636736 (.node 188879601664 (.node 184180473856 .nil .nil) (.node 195831906304 .nil .nil)) (.node 200954036224 (.node 197615681536 .nil .nil) .nil)))
        (.node 231820509184
          (.node 216304500736 (.node 205958987776 (.node 202867326976 .nil .nil) (.node 214172729344 .nil .nil)) (.node 222441865216 (.node 217356353536 .nil .nil) .nil))
          (.node 237594148864 (.node 235179311104 (.node 235062378496 .nil .nil) (.node 236821233664 .nil .nil)) (.node 240443490304 (.node 240180527104 .nil .nil) .nil))))))

private def scan : ℕ → ℕ → Bool
  | 0, _ => true
  | k+1, u => separated landmarks u && scan k (3*u % modulus)

set_option maxHeartbeats 10000000 in
private theorem blocks_pass (t : Fin 64) :
    scan 64 (3^(8+64*t.val) % modulus) = true := by
  fin_cases t <;> decide +kernel

private theorem residues_four : ∀ j : Fin 116,
    let v := 4^(7+j.val) % modulus
    containsResidue landmarks v = true ∧ 3501 ≤ v ∧ v+3501 ≤ modulus := by
  decide +kernel

private lemma scan_sound (k s j : ℕ) (hj : j < k) (h : scan k (3^s % modulus) = true) :
    separated landmarks (3^(s+j) % modulus) = true := by
  induction k generalizing s j with
  | zero => omega
  | succ k ih =>
    obtain ⟨here, later⟩ := Bool.and_eq_true_iff.mp h
    cases j with
    | zero => simpa using here
    | succ j =>
      have next : 3 * (3^s % modulus) % modulus = 3^(s+1) % modulus := by
        rw [Nat.mul_mod_mod, pow_succ, Nat.mul_comm]
      rw [next] at later
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (s+1) j (by omega) later

private lemma cycle_power (d start period : ℕ) (positive : 0 < period)
    (cycle : d^(start+period) % modulus = d^start % modulus) (n : ℕ) :
    d^(start+n) % modulus = d^(start + n%period) % modulus := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < period
    · rw [Nat.mod_eq_of_lt hn]
    · have hn' : period ≤ n := by omega
      calc d^(start+n) % modulus = (d^(start+period) * d^(n-period)) % modulus := by
             rw [← pow_add]
             congr 2
             omega
           _ = (d^start * d^(n-period)) % modulus := by
             rw [Nat.mul_mod, cycle, ← Nat.mul_mod]
           _ = d^(start+(n-period)) % modulus := by rw [pow_add]
           _ = d^(start+(n-period)%period) % modulus := ih _ (by omega)
           _ = d^(start+n%period) % modulus := by rw [← Nat.mod_eq_sub_mod hn']

private lemma lift_separation (u v : ℕ)
    (lo : 3501 ≤ v%modulus) (hi : v%modulus+3501 ≤ modulus)
    (h : u%modulus + 3501 ≤ v%modulus ∨ v%modulus + 2334 ≤ u%modulus) :
    u + 3501 ≤ v ∨ v + 2334 ≤ u := by
  have hu := Nat.mod_lt u (by decide : 0 < modulus)
  have h₁ := Nat.div_add_mod u modulus
  have h₂ := Nat.div_add_mod v modulus
  by_cases hq : u/modulus = v/modulus
  · unfold modulus at *
    omega
  · rcases lt_or_gt_of_ne hq with hlt | hgt <;> unfold modulus at * <;> omega

private lemma large_separation (p q : ℕ) (hp : 8 ≤ p) (hq : 7 ≤ q) :
    3^p + 3501 ≤ 4^q ∨ 4^q + 2334 ≤ 3^p := by
  have ucycle := cycle_power 3 8 4096 (by decide) (by decide +kernel) (p-8)
  have vcycle := cycle_power 4 7 116 (by decide) (by decide +kernel) (q-7)
  rw [show 8+(p-8) = p by omega] at ucycle
  rw [show 7+(q-7) = q by omega] at vcycle
  have hu : separated landmarks (3^p % modulus) = true := by
    rw [ucycle]
    let j := (p-8)%4096
    have hj : j < 4096 := Nat.mod_lt _ (by decide)
    have pass := blocks_pass ⟨j/64, by omega⟩
    have h := scan_sound 64 (8+64*(j/64)) (j%64) (Nat.mod_lt _ (by decide)) pass
    change separated landmarks (3^(8+j) % modulus) = true
    simpa only [show 8 + 64 * (j / 64) + j % 64 = 8+j by omega] using h
  obtain ⟨hv, hlo, hhi⟩ := residues_four ⟨(q-7)%116, Nat.mod_lt _ (by decide)⟩
  apply lift_separation
  · simpa only [vcycle] using hlo
  · simpa only [vcycle] using hhi
  · exact separated_sound landmarks _ _ hu (by simpa only [vcycle] using hv)

theorem gap347 (a b c : ℕ) (ha : 7 ≤ a) (hb : 5 ≤ b) (_hc : 3 ≤ c) :
    let u := 3^(a+1)
    let v := 4^(b+1)
    let w := 7^(c+1)
    6*min u (min v w) + 7002 ≤ 3*u+2*v+w := by
  dsimp only
  have sep : 3^(a+1) + 3501 ≤ 4^(b+1) ∨ 4^(b+1) + 2334 ≤ 3^(a+1) := by
    by_cases hq : 7 ≤ b+1
    · exact large_separation _ _ (by omega) hq
    · have he : b = 5 := by omega
      subst b
      right
      calc 4^(5+1) + 2334 ≤ 3^8 := by decide
           _ ≤ 3^(a+1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end OMA.Powers347

theorem OMA.solution : type_of% @Erdos124.erdos124.ne_zero_three_four_seven := by
  exact OMA.Powers347.eventually_of_gap OMA.Powers347.gap347
