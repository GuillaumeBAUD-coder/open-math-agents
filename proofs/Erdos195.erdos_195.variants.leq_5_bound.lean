import FormalConjectures.ErdosProblems.«195»
import Mathlib.Order.OrderIsoNat

/-! Geneson, arXiv:1803.06334, Proposition 1. Order the integers by powers-of-ten
shells and use a parity-first order with no three-term progression inside each shell. -/

namespace OMA

private def revBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => x % 2 * 2 ^ k + revBits k (x / 2)

private lemma revBits_lt (k x : ℕ) : revBits k x < 2 ^ k := by
  induction k generalizing x with
  | zero => simp [revBits]
  | succ k ih =>
    have h := ih (x / 2)
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hmod with hmod | hmod <;> simp only [revBits, hmod, zero_mul, one_mul,
      zero_add, pow_succ'] <;> omega

private lemma revBits_parity_le {k a b : ℕ} (h : revBits (k + 1) a ≤ revBits (k + 1) b) :
    a % 2 ≤ b % 2 := by
  by_contra! hn
  have ha : a % 2 = 1 := by omega
  have hb : b % 2 = 0 := by omega
  have hbound := revBits_lt k (b / 2)
  simp only [revBits, ha, hb, one_mul, zero_mul, zero_add] at h
  omega

private lemma revBits_inj {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (he : revBits k a = revBits k b) : a = b := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero] at ha hb
    omega
  | succ k ih =>
    have hmod := le_antisymm (revBits_parity_le he.le) (revBits_parity_le he.ge)
    simp only [revBits, hmod, Nat.add_left_cancel_iff] at he
    simp only [pow_succ'] at ha hb
    have hdiv := ih (a := a / 2) (b := b / 2) (by omega) (by omega) he
    omega

private lemma revBits_no_ap {k a b c : ℕ} (hap : a + c = 2 * b)
    (hab : revBits k a < revBits k b) (hbc : revBits k b < revBits k c) : False := by
  induction k generalizing a b c with
  | zero => exact (lt_irrefl 0) hab
  | succ k ih =>
    have hac : a % 2 = c % 2 := by omega
    have hmodab : a % 2 = b % 2 := le_antisymm (revBits_parity_le hab.le)
      (hac ▸ revBits_parity_le hbc.le)
    have hmodbc : b % 2 = c % 2 := hmodab.symm.trans hac
    simp only [revBits, hmodab, Nat.add_lt_add_iff_left] at hab
    simp only [revBits, hmodbc, Nat.add_lt_add_iff_left] at hbc
    exact ih (by omega) hab hbc

private lemma exists_shell (z : ℤ) : ∃ j : ℕ, z.natAbs < 10 ^ j :=
  ⟨z.natAbs, (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by decide) _)⟩

private def shell (z : ℤ) : ℕ := Nat.find (exists_shell z)

private lemma abs_lt_shell (z : ℤ) : z.natAbs < 10 ^ shell z :=
  Nat.find_spec (exists_shell z)

private lemma shell_le {z : ℤ} {j : ℕ} (h : z.natAbs < 10 ^ j) : shell z ≤ j :=
  Nat.find_min' (exists_shell z) h

private lemma abs_of_prior_shell {x y : ℤ} (h : shell x < shell y) :
    x.natAbs < 10 ^ (shell y - 1) :=
  (abs_lt_shell x).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

private def shifted (j : ℕ) (z : ℤ) : ℕ := (z + (10 ^ j : ℕ)).toNat

private lemma shifted_int {j : ℕ} {z : ℤ} (h : z.natAbs < 10 ^ j) :
    (shifted j z : ℤ) = z + (10 ^ j : ℕ) := by
  have hh : (z.natAbs : ℤ) < (10 ^ j : ℕ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hh
  have hneg := neg_abs_le z
  exact Int.toNat_of_nonneg (by omega)

private lemma shifted_lt {j : ℕ} {z : ℤ} (h : z.natAbs < 10 ^ j) :
    shifted j z < 2 * 10 ^ j := by
  have hh : (z.natAbs : ℤ) < (10 ^ j : ℕ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hh
  have hz := le_abs_self z
  have he := shifted_int h
  exact_mod_cast (show (shifted j z : ℤ) < 2 * ((10 ^ j : ℕ) : ℤ) by omega)

private def key (z : ℤ) : ℕ :=
  2 ^ (2 * 10 ^ shell z) + revBits (2 * 10 ^ shell z) (shifted (shell z) z)

private lemma key_lt_of_shell_lt {x y : ℤ} (h : shell x < shell y) : key x < key y := by
  have hx : key x < 2 ^ (2 * 10 ^ shell x + 1) := by
    rw [key, pow_succ']
    have hh := revBits_lt (2 * 10 ^ shell x) (shifted (shell x) x)
    omega
  have hpow : 10 ^ shell x < 10 ^ shell y := Nat.pow_lt_pow_right (by decide) h
  have hy : 2 ^ (2 * 10 ^ shell y) ≤ key y := Nat.le_add_right _ _
  exact hx.trans_le ((Nat.pow_le_pow_right (by decide) (by omega)).trans hy)

private lemma shell_le_of_key_lt {x y : ℤ} (h : key x < key y) : shell x ≤ shell y :=
  le_of_not_gt fun hn => (key_lt_of_shell_lt hn).not_gt h

private lemma key_inj : Function.Injective key := by
  intro x y he
  have hs : shell x = shell y := by
    apply le_antisymm <;> apply le_of_not_gt <;>
      intro hh <;> have := key_lt_of_shell_lt hh <;> omega
  simp only [key, hs, Nat.add_left_cancel_iff] at he
  have hx : x.natAbs < 10 ^ shell y := hs ▸ abs_lt_shell x
  have hy := abs_lt_shell y
  have hbits := revBits_inj ((shifted_lt hx).trans (Nat.lt_two_pow_self))
    ((shifted_lt hy).trans (Nat.lt_two_pow_self)) he
  have hshiftx := shifted_int hx
  have hshifty := shifted_int hy
  omega

private lemma same_shell_no_ap {a b c : ℤ} (hap : a + c = 2 * b)
    (hab : key a < key b) (hbc : key b < key c)
    (hsab : shell a = shell b) (hsbc : shell b = shell c) : False := by
  have ha : a.natAbs < 10 ^ shell c := (hsab.trans hsbc) ▸ abs_lt_shell a
  have hb : b.natAbs < 10 ^ shell c := hsbc ▸ abs_lt_shell b
  have hc := abs_lt_shell c
  have hsa := shifted_int ha
  have hsb := shifted_int hb
  have hsc := shifted_int hc
  have hnat : shifted (shell c) a + shifted (shell c) c = 2 * shifted (shell c) b := by omega
  simp only [key, hsab, hsbc, Nat.add_lt_add_iff_left] at hab hbc
  exact revBits_no_ap hnat hab hbc

private lemma step_bound {a d : ℤ} {m : ℕ}
    (ha : a.natAbs < m) (hb : (a + d).natAbs < m) :
    d.natAbs < 2 * m := by
  have h := Int.natAbs_add_le (a + d) (-a)
  have he : a + d + -a = d := by omega
  rw [he, Int.natAbs_neg] at h
  omega

private lemma transition_no_ap {w d : ℤ} {j : ℕ} (hj : 0 < j)
    (hw : w.natAbs < 10 ^ (j - 1)) (hd : d.natAbs < 2 * 10 ^ (j - 1))
    (hs : shell (w + d) = j)
    (h₁ : key (w + d) < key (w + d + d))
    (h₂ : key (w + d + d) < key (w + d + d + d)) : False := by
  have hpow : 10 ^ j = 10 ^ (j - 1) * 10 := by
    rw [← pow_succ]
    congr 1
    omega
  have hu := Int.natAbs_add_le w d
  have hv := Int.natAbs_add_le (w + d) d
  have ht := Int.natAbs_add_le (w + d + d) d
  have hv' : (w + d + d).natAbs < 10 ^ j := by rw [hpow]; omega
  have ht' : (w + d + d + d).natAbs < 10 ^ j := by rw [hpow]; omega
  have hsv : shell (w + d + d) = j := by
    apply le_antisymm (shell_le hv')
    exact hs ▸ shell_le_of_key_lt h₁
  have hst : shell (w + d + d + d) = j := by
    apply le_antisymm (shell_le ht')
    exact hsv ▸ shell_le_of_key_lt h₂
  exact same_shell_no_ap (by omega) h₁ h₂ (hs.trans hsv.symm) (hsv.trans hst.symm)

private lemma no_six_keys (a d : ℤ)
    (h₀ : key a < key (a + d))
    (h₁ : key (a + d) < key (a + 2 * d))
    (h₂ : key (a + 2 * d) < key (a + 3 * d))
    (h₃ : key (a + 3 * d) < key (a + 4 * d))
    (h₄ : key (a + 4 * d) < key (a + 5 * d)) : False := by
  have hs₀ := shell_le_of_key_lt h₀
  have hs₁ := shell_le_of_key_lt h₁
  have hs₂ := shell_le_of_key_lt h₂
  rcases hs₁.lt_or_eq with hs₁ | hs₁
  · have hd := step_bound (abs_of_prior_shell (hs₀.trans_lt hs₁)) (abs_of_prior_shell hs₁)
    apply transition_no_ap (w := a + d) (d := d) (j := shell (a + 2 * d))
      (by omega) (abs_of_prior_shell hs₁) hd
    · (congr 1; ring)
    · convert h₂ using 2
      all_goals ring
    · convert h₃ using 2
      all_goals ring
  · rcases hs₂.lt_or_eq with hs₂ | hs₂
    · have hbefore := hs₁.trans_lt hs₂
      have hd := step_bound (abs_of_prior_shell (hs₀.trans_lt hbefore))
        (abs_of_prior_shell hbefore)
      apply transition_no_ap (w := a + 2 * d) (d := d) (j := shell (a + 3 * d))
        (by omega) (abs_of_prior_shell hs₂) hd
      · (congr 1; ring)
      · convert h₃ using 2
        all_goals ring
      · convert h₄ using 2
        all_goals ring
    · exact same_shell_no_ap (by ring) h₁ h₂ hs₁ hs₂

private noncomputable def orderedIntegers : ℕ ≃ ℤ := by
  letI : Infinite (Set.range key) := (Set.infinite_range_of_injective key_inj).to_subtype
  exact (Nat.Subtype.orderIsoOfNat (Set.range key)).toEquiv.trans (Equiv.ofInjective key key_inj).symm

private lemma orderedIntegers_key : StrictMono fun n : ℕ => key (orderedIntegers n) := by
  let : Infinite (Set.range key) := (Set.infinite_range_of_injective key_inj).to_subtype
  let e := Nat.Subtype.orderIsoOfNat (Set.range key)
  intro m n hmn
  have hval (i : ℕ) : key (orderedIntegers i) = (e i).val := by
    exact congrArg Subtype.val ((Equiv.ofInjective key key_inj).apply_symm_apply (e i))
  change key (orderedIntegers m) < key (orderedIntegers n)
  rw [hval, hval]
  exact e.strictMono hmn

private lemma range_pair {r : ℤ → ℤ → Prop} {k i j : ℕ} {a d : ℤ}
    (h : ((List.range k).map fun n => a + n • d).Pairwise r)
    (hij : i < j) (hjk : j < k) : r (a + (i : ℤ) * d) (a + (j : ℤ) * d) := by
  have hi : i < ((List.range k).map fun n => a + n • d).length := by
    simpa using hij.trans hjk
  have hj : j < ((List.range k).map fun n => a + n • d).length := by simpa using hjk
  simpa only [List.getElem_map, List.getElem_range, nsmul_eq_mul] using
    (List.pairwise_iff_getElem.mp h) i j hi hj hij

private lemma no_long_ap {k : ℕ} (hk : 6 ≤ k) :
    ¬ HasMonotoneAP orderedIntegers k := by
  rintro ⟨l, ⟨a, d, hap⟩, hp⟩
  have hkeys : (l.map orderedIntegers).Pairwise (fun x y => key x < key y) :=
    List.pairwise_map.mpr (hp.imp fun h => orderedIntegers_key h)
  rcases hap with hforward | hreverse
  · rw [hforward] at hkeys
    have h₀ := range_pair hkeys (i := 0) (j := 1) (by decide) (by omega)
    have h₁ := range_pair hkeys (i := 1) (j := 2) (by decide) (by omega)
    have h₂ := range_pair hkeys (i := 2) (j := 3) (by decide) (by omega)
    have h₃ := range_pair hkeys (i := 3) (j := 4) (by decide) (by omega)
    have h₄ := range_pair hkeys (i := 4) (j := 5) (by decide) (by omega)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, add_zero] at h₀ h₁ h₂ h₃ h₄
    exact no_six_keys a d h₀ h₁ h₂ h₃ h₄
  · rw [hreverse, List.map_reverse, List.pairwise_reverse] at hkeys
    have h₀ := range_pair hkeys (i := 0) (j := 1) (by decide) (by omega)
    have h₁ := range_pair hkeys (i := 1) (j := 2) (by decide) (by omega)
    have h₂ := range_pair hkeys (i := 2) (j := 3) (by decide) (by omega)
    have h₃ := range_pair hkeys (i := 3) (j := 4) (by decide) (by omega)
    have h₄ := range_pair hkeys (i := 4) (j := 5) (by decide) (by omega)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, add_zero] at h₀ h₁ h₂ h₃ h₄
    apply no_six_keys (a + 5 * d) (-d)
    · convert h₄ using 2
      all_goals ring
    · convert h₃ using 2
      all_goals ring
    · convert h₂ using 2
      all_goals ring
    · convert h₁ using 2
      all_goals ring
    · convert h₀ using 2
      all_goals ring

end OMA

theorem OMA.solution : type_of% @Erdos195.erdos_195.variants.leq_5_bound := by
  apply csSup_le'
  intro k hk
  by_contra hn
  exact OMA.no_long_ap (by omega) (hk orderedIntegers)