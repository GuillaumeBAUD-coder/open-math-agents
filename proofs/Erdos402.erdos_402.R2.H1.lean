import OMAReductions.R_Erdos402_erdos_402_R2
import Mathlib

/-!
Finite Graham bound through 7000. Elementary and configuration lemmas
adapted from Boris Alexeev's Lean development (formal authors Codex,
GPT-5.6 Sol), source blob f64dbcb0cb7d999a5205bdc380a23191b11d241b.
https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos402.lean
The finite verification here uses kernel-checked interval certificates,
a verified square-root primality test, and no native evaluator.
-/
namespace OMA.GrahamFinite
open scoped Pointwise
open Filter Asymptotics
private def quickPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (n.sqrt+1)).all (fun d => decide (d < 2 ∨ ¬d ∣ n))

private lemma quickPrime_spec (n : ℕ) : quickPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [quickPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  constructor
  · rintro ⟨hn,h⟩
    refine ⟨hn,fun d hd hd' => ?_⟩
    exact (h d (by omega)).resolve_left (by omega)
  · rintro ⟨hn,h⟩
    refine ⟨hn,fun d hd => ?_⟩
    by_cases h2 : d < 2
    · exact Or.inl h2
    · exact Or.inr (h d (by omega) (by omega))

private instance (priority := 2000) quickPrimeDecidable (n : ℕ) : Decidable n.Prime :=
  if h : quickPrime n = true then isTrue ((quickPrime_spec n).mp h)
  else isFalse (fun hp => h ((quickPrime_spec n).mpr hp))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def GrahamBound (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def hasGrahamBound (A : Finset ℕ) : Bool :=
  decide (∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma hasGrahamBound_eq_true (A : Finset ℕ) :
    hasGrahamBound A = true ↔ GrahamBound A := by
  simp [hasGrahamBound, GrahamBound]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def badSubsets (D : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  (D.powersetCard n).filter fun A ↦ hasGrahamBound A = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_badSubsets_eq_empty {D A : Finset ℕ} {n : ℕ}
    (hcert : badSubsets D n = ∅) (hsub : A ⊆ D) (hcard : A.card = n) :
    GrahamBound A := by
  by_contra hbad
  have hbool : hasGrahamBound A = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hbad ((hasGrahamBound_eq_true A).mp htrue)
  have hmem : A ∈ badSubsets D n := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hbool⟩
  rw [hcert] at hmem
  exact Finset.notMem_empty A hmem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma residue_inj_of_div_gcd_lt {p a b : ℕ} (hp : p.Prime)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hpa : ¬p ∣ a)
    (ha : a / a.gcd b < p) (hb : b / a.gcd b < p)
    (hc : (a : ZMod p) = (b : ZMod p)) : a = b := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := a.gcd b
  let x := a / g
  let y := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hxlt : x < p := ha
  have hylt : y < p := hb
  have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hpg : ¬p ∣ g := fun h ↦ hpa (h.trans (Nat.gcd_dvd_left a b))
  have hcg0 : (g : ZMod p) ≠ 0 := by
    intro hz
    exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
  have hc' : (g : ZMod p) * x = (g : ZMod p) * y := by
    calc
      (g : ZMod p) * x = ((g * x : ℕ) : ZMod p) := (Nat.cast_mul g x).symm
      _ = (a : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hga
      _ = (b : ZMod p) := hc
      _ = ((g * y : ℕ) : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hgb.symm
      _ = (g : ZMod p) * y := Nat.cast_mul g y
  have hxyZ : (x : ZMod p) = y := mul_left_cancel₀ hcg0 hc'
  have hxy : x = y := by
    have hv := congrArg ZMod.val hxyZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hv
  rw [← hga, ← hgb, hxy]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def foldedResidue (p a : ℕ) : ℕ :=
  min (a % p) (p - a % p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedResidue_pos {p a : ℕ} (hp : 0 < p) (hpa : ¬p ∣ a) :
    0 < foldedResidue p a := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  have hr0 : a % p ≠ 0 := by
    intro h
    exact hpa (Nat.dvd_of_mod_eq_zero h)
  unfold foldedResidue
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedResidue_le_div_two {p a : ℕ} (hp : 0 < p) :
    foldedResidue p a ≤ p / 2 := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  unfold foldedResidue
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedResidue_eq_iff {p a b : ℕ} (hp : 0 < p)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b)
    (h : foldedResidue p a = foldedResidue p b) :
    a % p = b % p ∨ a % p + b % p = p := by
  have halt : a % p < p := Nat.mod_lt a hp
  have hblt : b % p < p := Nat.mod_lt b hp
  have ha0 : a % p ≠ 0 := fun hz ↦ hpa (Nat.dvd_of_mod_eq_zero hz)
  have hb0 : b % p ≠ 0 := fun hz ↦ hpb (Nat.dvd_of_mod_eq_zero hz)
  unfold foldedResidue at h
  simp only [min_def] at h
  split at h <;> split at h <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private noncomputable def foldedMin (A : Finset ℕ) (p a : ℕ) : ℕ := by
  classical
  exact if ha : a ∈ A then
    (A.filter fun b ↦ foldedResidue p b = foldedResidue p a).min'
      ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_mem {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedMin A p a ∈ A := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_color {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedResidue p (foldedMin A p a) = foldedResidue p a := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  let S := A.filter fun b ↦ foldedResidue p b = foldedResidue p a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  exact (Finset.mem_filter.mp (S.min'_mem hS)).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_le {A : Finset ℕ} {p a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p b = foldedResidue p a) : foldedMin A p a ≤ b := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨hb, hcolor⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma foldedMin_eq_of_color {A : Finset ℕ} {p a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p a = foldedResidue p b) :
    foldedMin A p a = foldedMin A p b := by
  apply Nat.le_antisymm
  · apply foldedMin_le ha (foldedMin_mem hb)
    exact (foldedMin_color hb).trans hcolor.symm
  · apply foldedMin_le hb (foldedMin_mem ha)
    exact (foldedMin_color ha).trans hcolor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def representedMultipliers (A : Finset ℕ) (α β : ℕ) : Finset ℕ :=
  (A.image fun a ↦ a / α).filter fun d ↦ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma mem_representedMultipliers {A : Finset ℕ} {α β d : ℕ} (hα : 0 < α) :
    d ∈ representedMultipliers A α β ↔ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨α * d, h.2.1, ?_⟩, h⟩
    exact Nat.mul_div_cancel_left d hα

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representedMultipliers_nonzero {A : Finset ℕ} {α β : ℕ} (hα : 0 < α) :
    0 ∉ representedMultipliers A α β := by
  rw [mem_representedMultipliers hα]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def representationCount (A : Finset ℕ) (p α : ℕ) : ℕ :=
  (representedMultipliers A α (p - α)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def representationPairs (A : Finset ℕ) (p : ℕ) :
    Finset ((α : ℕ) × ℕ) :=
  (Finset.Icc ((p + 1) / 2) A.card).sigma fun α ↦
    representedMultipliers A α (p - α)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma zero_card_le_excess {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (h : S.card ≤ S.sum f) :
    (S.filter fun x ↦ f x = 0).card ≤
      (S.filter fun x ↦ 2 ≤ f x).sum fun x ↦ f x - 1 := by
  let Z := S.filter fun x ↦ f x = 0
  let M := S.filter fun x ↦ 2 ≤ f x
  have hZ : Z.card = ∑ x ∈ S, if f x = 0 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_filter (fun x ↦ f x = 0) (fun _ ↦ 1)
  have hM : M.sum (fun x ↦ f x - 1) =
      ∑ x ∈ S, if 2 ≤ f x then f x - 1 else 0 := by
    exact Finset.sum_filter (fun x ↦ 2 ≤ f x) (fun x ↦ f x - 1)
  have hid : S.sum f + Z.card = S.card + M.sum (fun x ↦ f x - 1) := by
    rw [hZ, hM, Finset.card_eq_sum_ones]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> omega
  change Z.card ≤ M.sum fun x ↦ f x - 1
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def normalize (A : Finset ℕ) : Finset ℕ :=
  A.image fun a ↦ a / A.gcd id

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_pos (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    0 < A.gcd id := by
  apply Nat.pos_of_ne_zero
  intro hg
  obtain ⟨a, ha⟩ := hA
  have := Finset.gcd_eq_zero_iff.mp hg a ha
  exact h₀ (this ▸ ha)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_card (A : Finset ℕ) : (normalize A).card = A.card := by
  classical
  rw [normalize, Finset.card_image_of_injOn]
  intro a ha b hb hab
  have hda : A.gcd id ∣ a := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) ha
    exact ⟨c, hc⟩
  have hdb : A.gcd id ∣ b := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) hb
    exact ⟨c, hc⟩
  exact (Nat.div_left_inj hda hdb).mp hab

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_mem (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) :
    a / A.gcd id ∈ normalize A := by
  classical
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_nonzero (A : Finset ℕ) (h₀ : 0 ∉ A) : 0 ∉ normalize A := by
  classical
  intro h
  obtain ⟨a, ha, hadiv⟩ := Finset.mem_image.mp h
  have hgda : A.gcd id ∣ a := Finset.gcd_dvd ha
  have ha0 : a ≠ 0 := fun hzero ↦ h₀ (hzero ▸ ha)
  have hdiv0 : a / A.gcd id ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hgda)
      (gcd_pos A h₀ ⟨a, ha⟩)
  exact hdiv0 hadiv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_gcd (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    (normalize A).gcd id = 1 := by
  classical
  unfold normalize
  rw [← Finset.gcd_eq_gcd_image]
  obtain ⟨a, ha⟩ := hA
  exact Finset.gcd_div_id_eq_one ha (fun h ↦ h₀ (h ▸ ha))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma div_gcd_lt_card_of_not_grahamBound (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (ha0 : a ≠ 0) : a / a.gcd b < A.card := by
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  rw [Nat.div_lt_iff_lt_mul hgpos]
  exact Nat.lt_of_not_ge fun h ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma prime_not_dvd_of_card_le (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hcard : A.card ≤ p) {a : ℕ} (ha : a ∈ A) : ¬p ∣ a := by
  intro hpa
  have hex : ∃ b ∈ A, ¬p ∣ b := by
    by_contra h
    push Not at h
    have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd fun b hb ↦ h b hb
    rw [hgcd] at hpgcd
    exact hp.not_dvd_one hpgcd
  obtain ⟨b, hb, hpb⟩ := hex
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hpg : ¬p ∣ a.gcd b := fun h ↦ hpb (h.trans (Nat.gcd_dvd_right a b))
  have hpquot : p ∣ a / a.gcd b := by
    have hprod : (a / a.gcd b) * a.gcd b = a :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hp_prod : p ∣ (a / a.gcd b) * a.gcd b := by
      rw [hprod]
      exact hpa
    exact (hp.dvd_mul.mp hp_prod).resolve_right hpg
  have hqpos : 0 < a / a.gcd b :=
    Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
  have hple : p ≤ a / a.gcd b := Nat.le_of_dvd hqpos hpquot
  have hlt := div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma prime_not_dvd_of_card_le_two_mul (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {q : ℕ} (hq : q.Prime)
    (hlarge : A.card ≤ 2 * q) {a : ℕ} (ha : a ∈ A) : ¬q ∣ a := by
  classical
  by_cases hcard : A.card ≤ q
  · exact prime_not_dvd_of_card_le A h₀ hgcd hbad hq hcard ha
  have hqn : q < A.card := Nat.lt_of_not_ge hcard
  intro hqa
  let C := A.filter fun x ↦ q ∣ x
  let V := A.filter fun x ↦ ¬q ∣ x
  let U := C.image fun x ↦ x / q
  have hCne : C.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hqa⟩⟩
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ x ∈ A, q ∣ x := by
      intro x hx
      by_contra hqx
      have : x ∈ V := Finset.mem_filter.mpr ⟨hx, hqx⟩
      simpa [h] using this
    have hqgcd : q ∣ A.gcd id := Finset.dvd_gcd hall
    rw [hgcd] at hqgcd
    exact hq.not_dvd_one hqgcd
  have hUne : U.Nonempty := hCne.image _
  have hUcard : U.card = C.card := by
    dsimp only [U]
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hqx : q ∣ x := (Finset.mem_filter.mp hx).2
    have hqy : q ∣ y := (Finset.mem_filter.mp hy).2
    exact (Nat.div_left_inj hqx hqy).mp hxy
  have hpartition : C.card + V.card = A.card := by
    simpa only [C, V] using
      (Finset.card_filter_add_card_filter_not (s := A) (p := fun x ↦ q ∣ x))
  have hcross : ∀ c ∈ C, ∀ v ∈ V, c / q ∣ v := by
    intro c hc v hv
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
    have hc0 : c ≠ 0 := fun hz ↦ h₀ (hz ▸ hcA)
    have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
    have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
    have hqquot : q ∣ c / c.gcd v := by
      have hprod : (c / c.gcd v) * c.gcd v = c :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
      have : q ∣ (c / c.gcd v) * c.gcd v := by simpa [hprod] using hqc
      exact (hq.dvd_mul.mp this).resolve_right hqg
    have hquotpos : 0 < c / c.gcd v :=
      Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
    have hquotlt : c / c.gcd v < A.card :=
      div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
    have hquoteq : c / c.gcd v = q := by
      obtain ⟨k, hk⟩ := hqquot
      have hkpos : 0 < k := by
        exact Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
      have hkle : k = 1 := by
        by_contra hk1
        have hk2 : 2 ≤ k := by omega
        have htwo : 2 * q ≤ c / c.gcd v := by
          calc
            2 * q = q * 2 := Nat.mul_comm 2 q
            _ ≤ q * k := Nat.mul_le_mul_left q hk2
            _ = c / c.gcd v := hk.symm
        omega
      simpa [hkle] using hk
    have hcprod : q * (c / q) = c := by
      simpa [mul_comm] using Nat.mul_div_cancel' hqc
    have hgprod : q * c.gcd v = c := by
      calc
        q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
        _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
    have hg : c.gcd v = c / q := Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
    rw [← hg]
    exact Nat.gcd_dvd_right c v
  have hcrossU : ∀ u ∈ U, ∀ v ∈ V, u ∣ v := by
    intro u hu v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
    exact hcross c hc v hv
  let u₀ := U.min' hUne
  let v₀ := V.min' hVne
  have hu₀ : u₀ ∈ U := U.min'_mem hUne
  have hv₀ : v₀ ∈ V := V.min'_mem hVne
  have hu₀pos : 0 < u₀ := by
    obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu₀
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    rw [← hcu]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hqc) hq.pos
  have hv₀pos : 0 < v₀ := by
    exact Nat.pos_of_ne_zero fun h ↦ h₀ (h ▸ (Finset.mem_filter.mp hv₀).1)
  let S₁ := U.image fun u ↦ v₀ / u
  let S₂ := (V.erase v₀).image fun v ↦ v / u₀
  have hS₁card : S₁.card = U.card := by
    dsimp only [S₁]
    rw [Finset.card_image_of_injOn]
    intro u hu w hw huw
    have huv : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hwv : w ∣ v₀ := hcrossU w hw v₀ hv₀
    have hu0 : 0 < u := by
      exact Nat.pos_of_dvd_of_pos huv hv₀pos
    have hquotpos : 0 < v₀ / u := Nat.div_pos (Nat.le_of_dvd hv₀pos huv) hu0
    change v₀ / u = v₀ / w at huw
    apply Nat.mul_left_cancel hquotpos
    calc
      (v₀ / u) * u = v₀ := Nat.div_mul_cancel huv
      _ = (v₀ / w) * w := (Nat.div_mul_cancel hwv).symm
      _ = (v₀ / u) * w := congrArg (fun z ↦ z * w) huw.symm
  have hS₂card : S₂.card = V.card - 1 := by
    dsimp only [S₂]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_erase_of_mem hv₀]
    · intro v hv w hw hvw
      have hvV : v ∈ V := Finset.mem_of_mem_erase hv
      have hwV : w ∈ V := Finset.mem_of_mem_erase hw
      have huv : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
      have huw : u₀ ∣ w := hcrossU u₀ hu₀ w hwV
      change v / u₀ = w / u₀ at hvw
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel huv).symm
        _ = (w / u₀) * u₀ := congrArg (fun z ↦ z * u₀) hvw
        _ = w := Nat.div_mul_cancel huw
  have hSdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨v, hv, huvEq⟩ := Finset.mem_image.mp hx₂
    have hvV : v ∈ V := Finset.mem_of_mem_erase hv
    have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
    have hv₀lt : v₀ < v := (V.min'_le v hvV).lt_of_ne (Ne.symm hvne)
    have hu₀le : u₀ ≤ u := U.min'_le u hu
    have huv₀ : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hu₀v : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
    have hvle : v ≤ v₀ := by
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel hu₀v).symm
        _ = (v₀ / u) * u₀ := by rw [huvEq]
        _ ≤ (v₀ / u) * u := Nat.mul_le_mul_left (v₀ / u) hu₀le
        _ = v₀ := Nat.div_mul_cancel huv₀
    exact (not_le_of_gt hv₀lt) hvle
  let R := S₁ ∪ S₂
  have hRcard : R.card = A.card - 1 := by
    dsimp only [R]
    rw [Finset.card_union_of_disjoint hSdisj, hS₁card, hS₂card, hUcard]
    have hVpos : 0 < V.card := Finset.card_pos.mpr hVne
    omega
  let T := (Finset.Ico 1 A.card).erase q
  have hratio_mem_T : ∀ u ∈ U, ∀ v ∈ V, v / u ∈ T := by
    intro u hu v hv
    have huv : u ∣ v := hcrossU u hu v hv
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hv0 : v ≠ 0 := fun h ↦ h₀ (h ▸ hvA)
    have hu0 : 0 < u := Nat.pos_of_dvd_of_pos huv (Nat.pos_of_ne_zero hv0)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · intro heq
      have hqratio : q ∣ v / u := heq ▸ dvd_refl q
      have hqv : q ∣ v := by
        rw [← Nat.div_mul_cancel huv]
        exact dvd_mul_of_dvd_left hqratio u
      exact (Finset.mem_filter.mp hv).2 hqv
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) huv) hu0
    · obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu
      have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
      have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
      have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
      have hg : c.gcd v = u := by
        have hgprod : q * c.gcd v = c := by
          have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
          have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
          have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
          have hqquot : q ∣ c / c.gcd v := by
            have hp : q ∣ (c / c.gcd v) * c.gcd v := by
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_left c v)]
              exact hqc
            exact (hq.dvd_mul.mp hp).resolve_right hqg
          have hquotpos : 0 < c / c.gcd v :=
            Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
          have hquotlt := div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
          obtain ⟨k, hk⟩ := hqquot
          have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
          have hkone : k = 1 := by
            by_contra hk1
            have hk2 : 2 ≤ k := by omega
            have htwo : 2 * q ≤ c / c.gcd v := by
              calc
                2 * q = q * 2 := Nat.mul_comm 2 q
                _ ≤ q * k := Nat.mul_le_mul_left q hk2
                _ = c / c.gcd v := hk.symm
            omega
          have hquoteq : c / c.gcd v = q := by simpa [hkone] using hk
          calc
            q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
            _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
        have hcprod : q * (c / q) = c := by
          simpa [mul_comm] using Nat.mul_div_cancel' hqc
        have hgg : c.gcd v = c / q :=
          Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
        simpa [hcu] using hgg
      have hlt := div_gcd_lt_card_of_not_grahamBound A hbad hvA hcA hv0
      rw [Nat.gcd_comm v c, hg] at hlt
      exact hlt
  have hRsub : R ⊆ T := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u hu v₀ hv₀
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u₀ hu₀ v (Finset.mem_of_mem_erase hv)
  have hqT : q ∈ Finset.Ico 1 A.card := Finset.mem_Ico.mpr ⟨hq.one_le, hqn⟩
  have hTcard : T.card = A.card - 2 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hqT, Nat.card_Ico]
    omega
  have hRupper : R.card ≤ A.card - 2 :=
    (Finset.card_le_card hRsub).trans_eq hTcard
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_mul_cross_of_coprime {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (hab : a.Coprime b) (hcd : c.Coprime d) :
    (a * c).gcd (b * d) = a.gcd d * b.gcd c := by
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _
      (Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hc))).ne'
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb))
  intro q
  have habf : min (a.factorization q) (b.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd ha hb)
    rw [hab.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (a.factorization q) (b.factorization q) at h
    exact h.symm
  have hcdf : min (c.factorization q) (d.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd hc hd)
    rw [hcd.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (c.factorization q) (d.factorization q) at h
    exact h.symm
  rw [Nat.factorization_gcd (Nat.mul_ne_zero ha hc) (Nat.mul_ne_zero hb hd),
    Nat.factorization_mul ha hc, Nat.factorization_mul hb hd,
    Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb),
    Nat.factorization_gcd ha hd, Nat.factorization_gcd hb hc]
  change min (a.factorization q + c.factorization q)
      (b.factorization q + d.factorization q) =
    min (a.factorization q) (d.factorization q) +
      min (b.factorization q) (c.factorization q)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma div_gcd_mul_right (x y c : ℕ) (hc : 0 < c) :
    (x * c) / (x * c).gcd (y * c) = x / x.gcd y := by
  rw [Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ hc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma coprime_prime_sub {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hαp : α < p) : α.Coprime (p - α) := by
  rw [Nat.coprime_sub_self_right hαp.le]
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hα hαp)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma factor_closeness {N α β d₁ d₂ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : N * N < 2 * (α * α))
    (hα₁₂ : (α * d₁) / (α * d₁).gcd (β * d₂) < N)
    (hα₂₁ : (α * d₂) / (α * d₂).gcd (β * d₁) < N)
    (hβ₁₂ : (β * d₁) / (β * d₁).gcd (α * d₂) < N)
    (hβ₂₁ : (β * d₂) / (β * d₂).gcd (α * d₁) < N) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α < N * d₂.gcd α ∧
    α * d₂.gcd α < N * d₁.gcd α ∧
    β * d₁.gcd β < N * d₂.gcd β ∧
    β * d₂.gcd β < N * d₁.gcd β := by
  let X₁ := d₁.gcd α
  let Y₁ := d₁.gcd β
  let X₂ := d₂.gcd α
  let Y₂ := d₂.gcd β
  have hX₁ : 0 < X₁ := Nat.gcd_pos_of_pos_left α hd₁
  have hY₁ : 0 < Y₁ := Nat.gcd_pos_of_pos_left β hd₁
  have hX₂ : 0 < X₂ := Nat.gcd_pos_of_pos_left α hd₂
  have hY₂ : 0 < Y₂ := Nat.gcd_pos_of_pos_left β hd₂
  have hXY₁ : X₁ * Y₁ ∣ d₁ := by
    apply (hαβ.gcd_both d₁ d₁).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₁ α
    · exact Nat.gcd_dvd_left d₁ β
  have hXY₂ : X₂ * Y₂ ∣ d₂ := by
    apply (hαβ.gcd_both d₂ d₂).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₂ α
    · exact Nat.gcd_dvd_left d₂ β
  let Z₁ := d₁ / (X₁ * Y₁)
  let Z₂ := d₂ / (X₂ * Y₂)
  have hZ₁ : 0 < Z₁ := Nat.div_pos (Nat.le_of_dvd hd₁ hXY₁)
    (Nat.mul_pos hX₁ hY₁)
  have hZ₂ : 0 < Z₂ := Nat.div_pos (Nat.le_of_dvd hd₂ hXY₂)
    (Nat.mul_pos hX₂ hY₂)
  have hd₁eq : d₁ = X₁ * Y₁ * Z₁ := by
    simpa [Z₁, mul_comm] using (Nat.div_mul_cancel hXY₁).symm
  have hd₂eq : d₂ = X₂ * Y₂ * Z₂ := by
    simpa [Z₂, mul_comm] using (Nat.div_mul_cancel hXY₂).symm
  have hgα₁₂ : (α * d₁).gcd (β * d₂) = X₂ * Y₁ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₁.ne' hd₂.ne' hαβ hd]
    simp only [X₂, Y₁, Nat.gcd_comm]
  have hgα₂₁ : (α * d₂).gcd (β * d₁) = X₁ * Y₂ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₂.ne' hd₁.ne' hαβ hd.symm]
    simp only [X₁, Y₂, Nat.gcd_comm]
  have hgβ₁₂ : (β * d₁).gcd (α * d₂) = Y₂ * X₁ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₁.ne' hd₂.ne' hαβ.symm hd]
    simp only [Y₂, X₁, Nat.gcd_comm]
  have hgβ₂₁ : (β * d₂).gcd (α * d₁) = Y₁ * X₂ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₂.ne' hd₁.ne' hαβ.symm hd.symm]
    simp only [Y₁, X₂, Nat.gcd_comm]
  have hiα₁₂ : α * X₁ * Z₁ < N * X₂ := by
    rw [hgα₁₂, Nat.div_lt_iff_lt_mul (Nat.mul_pos hX₂ hY₁)] at hα₁₂
    rw [hd₁eq] at hα₁₂
    apply (Nat.mul_lt_mul_right hY₁).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₁₂
  have hiα₂₁ : α * X₂ * Z₂ < N * X₁ := by
    rw [hgα₂₁, Nat.div_lt_iff_lt_mul (Nat.mul_pos hX₁ hY₂)] at hα₂₁
    rw [hd₂eq] at hα₂₁
    apply (Nat.mul_lt_mul_right hY₂).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₂₁
  have hprod : α * α * (Z₁ * Z₂) < N * N := by
    have hm := mul_lt_mul hiα₁₂ hiα₂₁.le
      (Nat.mul_pos (Nat.mul_pos hα hX₂) hZ₂) (Nat.zero_le (N * X₂))
    have hm' : (α * α * (Z₁ * Z₂)) * (X₁ * X₂) <
        (N * N) * (X₁ * X₂) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.mul_lt_mul_right (Nat.mul_pos hX₁ hX₂)).mp hm'
  have hZone : Z₁ * Z₂ = 1 := by
    have hlt : α * α * (Z₁ * Z₂) < α * α * 2 := by
      exact hprod.trans (by simpa only [mul_comm] using hsq)
    have hlt' : Z₁ * Z₂ < 2 :=
      (Nat.mul_lt_mul_left (Nat.mul_pos hα hα)).mp hlt
    have hpos : 0 < Z₁ * Z₂ := Nat.mul_pos hZ₁ hZ₂
    omega
  have hz₁one : Z₁ = 1 := Nat.dvd_one.mp ⟨Z₂, hZone.symm⟩
  have hz₂one : Z₂ = 1 :=
    Nat.dvd_one.mp ⟨Z₁, by simpa [mul_comm] using hZone.symm⟩
  have hd₁fac : d₁ = X₁ * Y₁ := by simpa [hz₁one] using hd₁eq
  have hd₂fac : d₂ = X₂ * Y₂ := by simpa [hz₂one] using hd₂eq
  have hiβ₁₂ : β * Y₁ < N * Y₂ := by
    rw [hgβ₁₂, Nat.div_lt_iff_lt_mul (Nat.mul_pos hY₂ hX₁)] at hβ₁₂
    rw [hd₁fac] at hβ₁₂
    apply (Nat.mul_lt_mul_right hX₁).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₁₂
  have hiβ₂₁ : β * Y₂ < N * Y₁ := by
    rw [hgβ₂₁, Nat.div_lt_iff_lt_mul (Nat.mul_pos hY₁ hX₂)] at hβ₂₁
    rw [hd₂fac] at hβ₂₁
    apply (Nat.mul_lt_mul_right hX₂).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₂₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [X₁, Y₁] using hd₁fac
  · simpa only [X₂, Y₂] using hd₂fac
  · simpa only [X₁, X₂] using (by simpa [hz₁one] using hiα₁₂)
  · simpa only [X₁, X₂] using (by simpa [hz₂one] using hiα₂₁)
  · simpa only [Y₁, Y₂] using hiβ₁₂
  · simpa only [Y₁, Y₂] using hiβ₂₁

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma factor_closeness_of_counterexample (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d₁ d₂ c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : 0 < c)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : A.card * A.card < 2 * (α * α))
    (hαd₁ : α * d₁ * c ∈ A) (hβd₁ : β * d₁ * c ∈ A)
    (hαd₂ : α * d₂ * c ∈ A) (hβd₂ : β * d₂ * c ∈ A) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α < A.card * d₂.gcd α ∧
    α * d₂.gcd α < A.card * d₁.gcd α ∧
    β * d₁.gcd β < A.card * d₂.gcd β ∧
    β * d₂.gcd β < A.card * d₁.gcd β := by
  apply factor_closeness hα hβ hd₁ hd₂ hαβ hd hsq
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hαd₁ hβd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₁) (β * d₂) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hαd₂ hβd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₂) (β * d₁) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hβd₁ hαd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₁) (α * d₂) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hβd₂ hαd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₂) (α * d₁) c hc] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_quotients_sum_prime_of_folded_eq (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p a b : ℕ} (hp : p.Prime) (hlower : A.card < p)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hfold : foldedResidue p a = foldedResidue p b) :
    a / a.gcd b + b / a.gcd b = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpfree {x : ℕ} (hx : x ∈ A) : ¬p ∣ x :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) hx
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hb)
  have hqa : a / a.gcd b < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0).trans hlower
  have hqbRaw : b / b.gcd a < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad hb ha hb0).trans hlower
  have hqb : b / a.gcd b < p := by simpa [Nat.gcd_comm] using hqbRaw
  rcases foldedResidue_eq_iff hp.pos (hpfree ha) (hpfree hb) hfold with hsame | hsum
  · have hcast : (a : ZMod p) = (b : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' a b p).mpr hsame
    exact (hab (residue_inj_of_div_gcd_lt hp ha0 hb0 (hpfree ha)
      hqa hqb hcast)).elim
  · let g := a.gcd b
    let x := a / g
    let y := b / g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hpg : ¬p ∣ g := fun h ↦ (hpfree ha) (h.trans (Nat.gcd_dvd_left a b))
    have hcg0 : (g : ZMod p) ≠ 0 := by
      intro hz
      exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
    have hpab : p ∣ a + b := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, hsum, Nat.mod_self]
    have hcastsum : (a : ZMod p) + (b : ZMod p) = 0 := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact hpab
    have hfactor : (g : ZMod p) * ((x : ZMod p) + (y : ZMod p)) = 0 := by
      rw [mul_add]
      calc
        (g : ZMod p) * x + (g : ZMod p) * y =
            ((g * x : ℕ) : ZMod p) + ((g * y : ℕ) : ZMod p) := by
              rw [Nat.cast_mul, Nat.cast_mul]
        _ = (a : ZMod p) + (b : ZMod p) := by rw [hga, hgb]
        _ = 0 := hcastsum
    have hxycast : (x : ZMod p) + (y : ZMod p) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hcg0
    have hpxy : p ∣ x + y := by
      apply (ZMod.natCast_eq_zero_iff (x + y) p).mp
      simpa only [Nat.cast_add] using hxycast
    have hxpos : 0 < x :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hypos : 0 < y :=
      Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb0)) hgpos
    have hxlt : x < p := by simpa only [x, g] using hqa
    have hylt : y < p := by simpa only [y, g] using hqb
    have hxy : x + y = p :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hpxy (by omega)
    simpa only [g, x, y] using hxy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma card_J_le_representationPairs (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).card ≤ (representationPairs A p).card := by
  classical
  have hpfree {a : ℕ} (ha : a ∈ A) : ¬p ∣ a :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) ha
  let R := A.filter fun a ↦ foldedMin A p a = a
  let E := A.filter fun a ↦ foldedMin A p a ≠ a
  have hpartition : R.card + E.card = A.card := by
    simpa only [R, E] using
      (Finset.card_filter_add_card_filter_not
        (s := A) (p := fun a ↦ foldedMin A p a = a))
  let color : {a // a ∈ R} → Fin (p / 2) := fun a ↦
    ⟨foldedResidue p a.1 - 1, by
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hpos := foldedResidue_pos hp.pos (hpfree haA)
      have hle := foldedResidue_le_div_two (a := a.1) hp.pos
      omega⟩
  have hcolor : Function.Injective color := by
    intro a b hab
    apply Subtype.ext
    have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
    have hbA : b.1 ∈ A := (Finset.mem_filter.mp b.2).1
    have hapos := foldedResidue_pos hp.pos (hpfree haA)
    have hbpos := foldedResidue_pos hp.pos (hpfree hbA)
    have hval := congrArg Fin.val hab
    have hfold : foldedResidue p a.1 = foldedResidue p b.1 := by
      dsimp only [color] at hval
      omega
    have hmins := foldedMin_eq_of_color haA hbA hfold
    have harep : foldedMin A p a.1 = a.1 := (Finset.mem_filter.mp a.2).2
    have hbrep : foldedMin A p b.1 = b.1 := (Finset.mem_filter.mp b.2).2
    exact harep.symm.trans (hmins.trans hbrep)
  have hRcard : R.card ≤ p / 2 := by
    have hle := Fintype.card_le_of_injective color hcolor
    simpa using hle
  have hpne : p ≠ 2 := by
    intro hp2
    rw [hp2] at hlower hupper
    omega
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hpne)
  have hJcard : (Finset.Icc ((p + 1) / 2) A.card).card = A.card - p / 2 := by
    rw [Nat.card_Icc]
    omega
  have hJleE : (Finset.Icc ((p + 1) / 2) A.card).card ≤ E.card := by
    rw [hJcard]
    omega
  let collisionMap : ℕ → ((α : ℕ) × ℕ) := fun a ↦
    ⟨a / (foldedMin A p a).gcd a, (foldedMin A p a).gcd a⟩
  have hmaps : Set.MapsTo collisionMap (↑E : Set ℕ) (↑(representationPairs A p)) := by
    intro a haE
    have haE' : a ∈ E := haE
    have haA : a ∈ A := (Finset.mem_filter.mp haE').1
    have hne : foldedMin A p a ≠ a := (Finset.mem_filter.mp haE').2
    let b := foldedMin A p a
    let g := b.gcd a
    have hbA : b ∈ A := foldedMin_mem haA
    have hfold : foldedResidue p b = foldedResidue p a := foldedMin_color haA
    have hble : b ≤ a := foldedMin_le haA haA rfl
    have hblt : b < a := hble.lt_of_ne hne
    have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hbA)
    have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ haA)
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hb0)
    have hgb : (b / g) * g = b := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left b a)
    have hga : (a / g) * g = a := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right b a)
    have hsum : b / g + a / g = p := by
      simpa only [b, g] using gcd_quotients_sum_prime_of_folded_eq A h₀ hgcd hbad hp
        hlower hbA haA hne hfold
    have hquotorder : b / g < a / g := by
      apply (Nat.mul_lt_mul_right hgpos).mp
      simpa only [hgb, hga] using hblt
    have hαpos : 0 < a / g := by omega
    have hαlower : (p + 1) / 2 ≤ a / g := by omega
    have hαlt : a / g < A.card := by
      have h := div_gcd_lt_card_of_not_grahamBound A hbad haA hbA ha0
      simpa only [g, Nat.gcd_comm] using h
    have hβ : p - a / g = b / g := by omega
    change (⟨a / g, g⟩ : (α : ℕ) × ℕ) ∈ representationPairs A p
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hαlower, hαlt.le⟩, ?_⟩
    rw [mem_representedMultipliers hαpos]
    refine ⟨hgpos, ?_, ?_⟩
    · rw [hga]
      exact haA
    rw [hβ]
    rw [hgb]
    exact hbA
  have hinj : Set.InjOn collisionMap (↑E : Set ℕ) := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : (α : ℕ) × ℕ ↦ z.1 * z.2) hab
    dsimp only [collisionMap] at hprod
    calc
      a = (a / (foldedMin A p a).gcd a) * (foldedMin A p a).gcd a :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p a) a)).symm
      _ = (b / (foldedMin A p b).gcd b) * (foldedMin A p b).gcd b := hprod
      _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p b) b)
  exact hJleE.trans (Finset.card_le_card_of_injOn collisionMap hmaps hinj)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma zero_card_le_representation_excess (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).sum fun α ↦ representationCount A p α - 1 := by
  apply zero_card_le_excess
  calc
    (Finset.Icc ((p + 1) / 2) A.card).card ≤
        (representationPairs A p).card :=
      card_J_le_representationPairs A h₀ hgcd hbad hp hlower hupper
    _ = (Finset.Icc ((p + 1) / 2) A.card).sum
        (representationCount A p) := by
      rw [representationPairs, Finset.card_sigma]
      rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_normalize (A : Finset ℕ)
    (h : GrahamBound (normalize A)) : GrahamBound A := by
  classical
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha₀
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb₀
  refine ⟨a, ha, b, hb, ?_⟩
  have hga : A.gcd id ∣ a := Finset.gcd_dvd ha
  have hgb : A.gcd id ∣ b := Finset.gcd_dvd hb
  have hggcd : A.gcd id ∣ a.gcd b := Nat.dvd_gcd hga hgb
  have hcard : (normalize A).card = A.card := normalize_card A
  rw [hcard, Nat.gcd_div hga hgb] at hab
  have hmul := Nat.mul_le_mul_right (A.gcd id) hab
  simpa only [mul_assoc, Nat.div_mul_cancel hggcd, Nat.div_mul_cancel hga] using hmul

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma lcm_div_gcd_eq (a : ℕ) (ha : a ≠ 0) (S : Finset ℕ) :
    S.lcm (fun b ↦ a / a.gcd b) = a / a.gcd (S.gcd id) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.div_self (Nat.pos_of_ne_zero ha)]
  | @insert b S hb ih =>
      rw [Finset.lcm_insert, Finset.gcd_insert, ih]
      change Nat.lcm (a / a.gcd b) (a / a.gcd (S.gcd id)) =
        a / a.gcd (b.gcd (S.gcd id))
      rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left a b)
        (Nat.gcd_dvd_left a (S.gcd id))]
      have hden : (a.gcd b).gcd (a.gcd (S.gcd id)) =
          a.gcd (b.gcd (S.gcd id)) := by
        rw [Nat.gcd_assoc, Nat.gcd_left_comm b a (S.gcd id), ← Nat.gcd_assoc,
          Nat.gcd_self]
      rw [hden]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalize_represented_dvd_product (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hD : (representedMultipliers A α β).Nonempty) :
    ∀ d ∈ normalize (representedMultipliers A α β), d ∣ α * β := by
  classical
  let D := representedMultipliers A α β
  let B := normalize D
  let c := D.gcd id
  have hD₀ : 0 ∉ D := representedMultipliers_nonzero hα
  have hc : 0 < c := gcd_pos D hD₀ hD
  have hBgcd : B.gcd id = 1 := normalize_gcd D hD₀ hD
  have hrepresented : ∀ {d}, d ∈ B →
      0 < d ∧ α * d * c ∈ A ∧ β * d * c ∈ A := by
    intro d hd
    change d ∈ D.image (fun e ↦ e / D.gcd id) at hd
    obtain ⟨e, heD, rfl⟩ := Finset.mem_image.mp hd
    have he := (mem_representedMultipliers hα).mp heD
    have hce : D.gcd id ∣ e := Finset.gcd_dvd heD
    have heq : e / D.gcd id * D.gcd id = e := Nat.div_mul_cancel hce
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd he.1 hce) hc
    · change α * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.1
    · change β * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.2
  intro d hdB
  have hdpos := (hrepresented hdB).1
  have hlocal : ∀ e ∈ B, d / d.gcd e ∣ α * β := by
    intro e heB
    have hepos := (hrepresented heB).1
    let g := d.gcd e
    let d' := d / g
    let e' := e / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
    have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hdpos) hg
    have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d hepos) hg
    have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
    have hdexpand : d' * (g * c) = d * c := by
      calc
        d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
        _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
    have heexpand : e' * (g * c) = e * c := by
      calc
        e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
        _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
    have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
      (Nat.mul_pos hg hc) hαβ hcop hsq
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.1)
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.2)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.1)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.2)
    change d' ∣ α * β
    rw [hfac.1]
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_right d' α) (Nat.gcd_dvd_right d' β)
  have hlcm : B.lcm (fun e ↦ d / d.gcd e) ∣ α * β := Finset.lcm_dvd hlocal
  rw [lcm_div_gcd_eq d hdpos.ne' B, hBgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma gcd_div_gcd_eq_component {α β d e : ℕ}
    (hαβ : α.Coprime β) (hd : 0 < d) (he : 0 < e)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β) :
    (d / d.gcd e).gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) := by
  let u := d.gcd α
  let v := d.gcd β
  let x := e.gcd α
  let y := e.gcd β
  have hu : 0 < u := Nat.gcd_pos_of_pos_left α hd
  have hv : 0 < v := Nat.gcd_pos_of_pos_left β hd
  have hx : 0 < x := Nat.gcd_pos_of_pos_left α he
  have hy : 0 < y := Nat.gcd_pos_of_pos_left β he
  have huα : u ∣ α := Nat.gcd_dvd_right d α
  have hvβ : v ∣ β := Nat.gcd_dvd_right d β
  have hxα : x ∣ α := Nat.gcd_dvd_right e α
  have hyβ : y ∣ β := Nat.gcd_dvd_right e β
  have huy : u.Coprime y := Nat.Coprime.of_dvd huα hyβ hαβ
  have hvx : v.Coprime x := Nat.Coprime.of_dvd hvβ hxα hαβ.symm
  have hgde : d.gcd e = u.gcd x * v.gcd y := by
    rw [hdfac, hefac]
    change (u * v).gcd (x * y) = u.gcd x * v.gcd y
    rw [mul_comm x y,
      gcd_mul_cross_of_coprime hu.ne' hy.ne' hv.ne' hx.ne' huy hvx]
    simp only [Nat.gcd_comm y v]
  have hdiv : d / d.gcd e =
      (u / u.gcd x) * (v / v.gcd y) := by
    rw [hgde, hdfac]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left u x)
      (Nat.gcd_dvd_left v y)).symm
  have huv : u / u.gcd x ∣ α :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left u x)).trans huα
  have hvv : v / v.gcd y ∣ β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left v y)).trans hvβ
  have hcop : (v / v.gcd y).Coprime α :=
    Nat.Coprime.of_dvd hvv dvd_rfl hαβ.symm
  rw [hdiv, mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hcop huv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma component_eq_of_gap_square_lt {N α x y : ℕ}
    (hα : 0 < α) (hαN : α ≤ N)
    (hx : 0 < x) (hy : 0 < y) (hxα : x ∣ α) (hyα : y ∣ α)
    (hgap : (N - α) * (N - α) < α)
    (hxy : α * (x / x.gcd y) < N * (y / x.gcd y))
    (hyx : α * (y / x.gcd y) < N * (x / x.gcd y)) : x = y := by
  let g := x.gcd y
  let X := x / g
  let Y := y / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hX : 0 < X := Nat.div_pos (Nat.gcd_le_left y hx) hg
  have hY : 0 < Y := Nat.div_pos (Nat.gcd_le_right x hy) hg
  have hcop : X.Coprime Y := Nat.coprime_div_gcd_div_gcd hg
  have hXα : X ∣ α := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxα
  have hYα : Y ∣ α := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hyα
  have hprod : X * Y ∣ α := hcop.mul_dvd_of_dvd_of_dvd hXα hYα
  have hprodLe : X * Y ≤ α := Nat.le_of_dvd hα hprod
  have hNsplit : N - α + α = N := Nat.sub_add_cancel hαN
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hXY : X < Y :=
      (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left x y)
        (Nat.gcd_dvd_right x y)).mpr hlt
    have hstep : α * (X + 1) < N * X := by
      apply (Nat.mul_le_mul_left α (Nat.succ_le_iff.mpr hXY)).trans_lt
      simpa only [g, X, Y] using hyx
    have hAX : α < (N - α) * X := by
      rw [← hNsplit, add_mul, mul_add] at hstep
      omega
    have hXsq : X * X ≤ α :=
      (Nat.mul_le_mul_left X hXY.le).trans hprodLe
    have hm := mul_lt_mul hgap hXsq
      (Nat.mul_pos hX hX) (Nat.zero_le α)
    have hm' : ((N - α) * X) * ((N - α) * X) < α * α := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.not_lt_of_ge (Nat.mul_self_lt_mul_self hAX).le) hm'
  · have hYX : Y < X :=
      (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_right x y)
        (Nat.gcd_dvd_left x y)).mpr hgt
    have hstep : α * (Y + 1) < N * Y := by
      apply (Nat.mul_le_mul_left α (Nat.succ_le_iff.mpr hYX)).trans_lt
      simpa only [g, X, Y] using hxy
    have hAY : α < (N - α) * Y := by
      rw [← hNsplit, add_mul, mul_add] at hstep
      omega
    have hYsq : Y * Y ≤ α :=
      (Nat.mul_le_mul_left Y hYX.le).trans (by
        simpa only [mul_comm X Y] using hprodLe)
    have hm := mul_lt_mul hgap hYsq
      (Nat.mul_pos hY hY) (Nat.zero_le α)
    have hm' : ((N - α) * Y) * ((N - α) * Y) < α * α := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.not_lt_of_ge (Nat.mul_self_lt_mul_self hAY).le) hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma scaled_component_closeness (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d e c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β)
    (hαd : α * d * c ∈ A) (hβd : β * d * c ∈ A)
    (hαe : α * e * c ∈ A) (hβe : β * e * c ∈ A) :
    α * (d.gcd α / (d.gcd α).gcd (e.gcd α)) <
        A.card * (e.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
    α * (e.gcd α / (d.gcd α).gcd (e.gcd α)) <
        A.card * (d.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
    β * (d.gcd β / (d.gcd β).gcd (e.gcd β)) <
        A.card * (e.gcd β / (d.gcd β).gcd (e.gcd β)) ∧
    β * (e.gcd β / (d.gcd β).gcd (e.gcd β)) <
        A.card * (d.gcd β / (d.gcd β).gcd (e.gcd β)) := by
  let g := d.gcd e
  let d' := d / g
  let e' := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hd) hg
  have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d he) hg
  have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
  have hdexpand : d' * (g * c) = d * c := by
    calc
      d' * (g * c) = (d' * g) * c := by rw [mul_assoc]
      _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
  have heexpand : e' * (g * c) = e * c := by
    calc
      e' * (g * c) = (e' * g) * c := by rw [mul_assoc]
      _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
    (Nat.mul_pos hg hc) hαβ hcop hsq
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hαd)
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hβd)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hαe)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hβe)
  have hdα : d'.gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) :=
    gcd_div_gcd_eq_component hαβ hd he hdfac hefac
  have heα : e'.gcd α = e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  have hdβ : d'.gcd β = d.gcd β / (d.gcd β).gcd (e.gcd β) :=
    gcd_div_gcd_eq_component hαβ.symm hd he
      (by simpa only [mul_comm] using hdfac)
      (by simpa only [mul_comm] using hefac)
  have heβ : e'.gcd β = e.gcd β / (d.gcd β).gcd (e.gcd β) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd β) (d.gcd β)] using
      (gcd_div_gcd_eq_component hαβ.symm he hd
        (by simpa only [mul_comm] using hefac)
        (by simpa only [mul_comm] using hdfac))
  have hα₁ := hfac.2.2.1
  have hα₂ := hfac.2.2.2.1
  have hβ₁ := hfac.2.2.2.2.1
  have hβ₂ := hfac.2.2.2.2.2
  rw [hdα, heα] at hα₁ hα₂
  rw [hdβ, heβ] at hβ₁ hβ₂
  exact ⟨hα₁, hα₂, hβ₁, hβ₂⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma triple_product_dvd_mul_pairwise_gcds {n x y z : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxn : x ∣ n) (hyn : y ∣ n) (hzn : z ∣ n)
    (hxyz : x.gcd (y.gcd z) = 1) :
    x * y * z ∣ n * x.gcd y * x.gcd z * y.gcd z := by
  rw [← Nat.factorization_le_iff_dvd
    (Nat.mul_ne_zero (Nat.mul_ne_zero hx.ne' hy.ne') hz.ne')
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.mul_ne_zero hn.ne'
        (Nat.gcd_pos_of_pos_left y hx).ne')
        (Nat.gcd_pos_of_pos_left z hx).ne')
      (Nat.gcd_pos_of_pos_left z hy).ne')]
  intro q
  have hxn' := (Nat.factorization_le_iff_dvd hx.ne' hn.ne').mpr hxn q
  have hyn' := (Nat.factorization_le_iff_dvd hy.ne' hn.ne').mpr hyn q
  have hzn' := (Nat.factorization_le_iff_dvd hz.ne' hn.ne').mpr hzn q
  have hmin := congrArg (fun f : ℕ →₀ ℕ ↦ f q)
    (Nat.factorization_gcd hx.ne'
      (Nat.gcd_pos_of_pos_left z hy).ne')
  rw [hxyz] at hmin
  simp only [Nat.factorization_one, Finsupp.inf_apply,
    Nat.factorization_gcd hy.ne' hz.ne'] at hmin
  rw [Nat.factorization_mul (Nat.mul_ne_zero hx.ne' hy.ne') hz.ne',
    Nat.factorization_mul hx.ne' hy.ne',
    Nat.factorization_mul
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne')
        (Nat.gcd_pos_of_pos_left z hx).ne')
      (Nat.gcd_pos_of_pos_left z hy).ne',
    Nat.factorization_mul
      (Nat.mul_ne_zero hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne')
      (Nat.gcd_pos_of_pos_left z hx).ne',
    Nat.factorization_mul hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne',
    Nat.factorization_gcd hx.ne' hy.ne',
    Nat.factorization_gcd hx.ne' hz.ne',
    Nat.factorization_gcd hy.ne' hz.ne']
  simp only [Finsupp.add_apply, Finsupp.inf_apply]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma reduced_divisors_diff_eq_one {N β y z : ℕ}
    (hβ : 0 < β) (hβN : β ≤ N)
    (hy : 0 < y) (hz : 0 < z) (hyz : y < z)
    (hyβ : y ∣ β) (hzβ : z ∣ β)
    (hgap : (N - β) * (N - β) ≤ 4 * N)
    (hclose : β * (z / y.gcd z) < N * (y / y.gcd z)) :
    z / y.gcd z = y / y.gcd z + 1 := by
  let g := y.gcd z
  let u := y / g
  let v := z / g
  let k := v - u
  have hg : 0 < g := Nat.gcd_pos_of_pos_left z hy
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left z hy) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right y hz) hg
  have huv : u < v :=
    (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left y z)
      (Nat.gcd_dvd_right y z)).mpr hyz
  have hk : 0 < k := Nat.sub_pos_of_lt huv
  have hvsplit : u + k = v := Nat.add_sub_of_le huv.le
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have huβ : u ∣ β := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left y z)).trans hyβ
  have hvβ : v ∣ β := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right y z)).trans hzβ
  have huvβ : u * v ∣ β := hcop.mul_dvd_of_dvd_of_dvd huβ hvβ
  have huvle : u * v ≤ β := Nat.le_of_dvd hβ huvβ
  have hN : 0 < N := hβ.trans_le hβN
  have hNsplit : N - β + β = N := Nat.sub_add_cancel hβN
  have hβk : β * k < (N - β) * u := by
    change β * v < N * u at hclose
    rw [← hvsplit, mul_add, ← hNsplit, add_mul] at hclose
    omega
  have hNk : N * k < (N - β) * v := by
    calc
      N * k = (β + (N - β)) * k := by rw [add_comm, hNsplit]
      _ = β * k + (N - β) * k := by rw [add_mul]
      _ < (N - β) * u + (N - β) * k :=
        Nat.add_lt_add_right hβk _
      _ = (N - β) * v := by rw [← hvsplit, mul_add]
  have hm := mul_lt_mul hβk hNk.le (Nat.mul_pos hN hk)
    (Nat.zero_le ((N - β) * u))
  have hm' : β * N * (k * k) <
      ((N - β) * (N - β)) * (u * v) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  have hright : ((N - β) * (N - β)) * (u * v) ≤
      (4 * N) * β := Nat.mul_le_mul hgap huvle
  have hkk : k * k < 4 := by
    apply (Nat.mul_lt_mul_left (Nat.mul_pos hβ hN)).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm'.trans_le hright
  have hkone : k = 1 := by
    have hklt : k < 2 := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [show 2 * 2 = 4 by norm_num] using hkk)
    omega
  simpa only [u, v, k, hkone] using hvsplit.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma spacing_polynomial_contradiction {N δ a b c : ℕ}
    (hN : 10 ≤ N) (hδ : 0 < δ) (ha : 0 < a) (hc : 0 < c)
    (hb : a + c = b) (hgap : δ * δ ≤ 4 * N)
    (hmain : (b * N) * (b * N) <
      (a * c * δ) * (δ * δ) + (b * N) * (c * δ)) : False := by
  have hNpos : 0 < N := by omega
  have hbpos : 0 < b := by omega
  let K := 4 * a + b
  have hfirst : (a * c * δ) * (δ * δ) ≤
      (a * c * δ) * (4 * N) := Nat.mul_le_mul_left _ hgap
  have hsmall : b * b * N < c * δ * K := by
    apply (Nat.mul_lt_mul_left hNpos).mp
    have ht := hmain.trans_le (Nat.add_le_add_right hfirst _)
    simpa only [K, mul_assoc, mul_comm, mul_left_comm,
      Nat.mul_add, Nat.add_mul] using ht
  have hsquare := Nat.mul_self_lt_mul_self hsmall
  have hright : (c * δ * K) * (c * δ * K) ≤
      4 * N * (c * c * (K * K)) := by
    have := Nat.mul_le_mul_left (c * c * (K * K)) hgap
    simpa only [mul_assoc, mul_comm, mul_left_comm] using this
  have hcore : b * b * b * b * N < 4 * c * c * (K * K) := by
    apply (Nat.mul_lt_mul_left hNpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      hsquare.trans_le hright
  have hmax : 16 * c * K ≤ 25 * (b * b) := by
    have hs : 0 ≤ (5 * (a : ℤ) - 3 * (c : ℤ)) ^ 2 := sq_nonneg _
    dsimp only [K]
    nlinarith
  have hmaxsq := Nat.mul_le_mul hmax hmax
  have hmaxsq' : 256 * (c * c * (K * K)) ≤
      625 * (b * b * b * b) := by
    calc
      256 * (c * c * (K * K)) = (16 * c * K) * (16 * c * K) := by ring
      _ ≤ (25 * (b * b)) * (25 * (b * b)) := hmaxsq
      _ = 625 * (b * b * b * b) := by ring
  have hscaled := (Nat.mul_lt_mul_left (by norm_num : 0 < 256)).mpr hcore
  have hfinal : 256 * N * (b * b * b * b) <
      2500 * (b * b * b * b) := by
    calc
      256 * N * (b * b * b * b) =
          256 * (b * b * b * b * N) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
      _ < 256 * (4 * c * c * (K * K)) := hscaled
      _ ≤ 4 * (625 * (b * b * b * b)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left 4 hmaxsq'
      _ = 2500 * (b * b * b * b) := by ring
  have hpowpos : 0 < b * b * b * b := by positivity
  have : 256 * N < 2500 := by
    apply (Nat.mul_lt_mul_right hpowpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma no_three_close_divisors {N β y₁ y₂ y₃ : ℕ}
    (hN : 10 ≤ N) (hβ : 0 < β) (hβN : β < N)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hy₃ : 0 < y₃)
    (h₁₂ : y₁ < y₂) (h₂₃ : y₂ < y₃)
    (hy₁β : y₁ ∣ β) (hy₂β : y₂ ∣ β) (hy₃β : y₃ ∣ β)
    (hgcd : y₁.gcd (y₂.gcd y₃) = 1)
    (hgap : (N - β) * (N - β) ≤ 4 * N)
    (hclose₁₂ : β * (y₂ / y₁.gcd y₂) < N * (y₁ / y₁.gcd y₂))
    (hclose₁₃ : β * (y₃ / y₁.gcd y₃) < N * (y₁ / y₁.gcd y₃))
    (hclose₂₃ : β * (y₃ / y₂.gcd y₃) < N * (y₂ / y₂.gcd y₃)) :
    False := by
  let a := y₁.gcd y₂
  let b := y₁.gcd y₃
  let c := y₂.gcd y₃
  let δ := N - β
  have ha : 0 < a := Nat.gcd_pos_of_pos_left y₂ hy₁
  have hb : 0 < b := Nat.gcd_pos_of_pos_left y₃ hy₁
  have hc : 0 < c := Nat.gcd_pos_of_pos_left y₃ hy₂
  have hδ : 0 < δ := Nat.sub_pos_of_lt hβN
  have hdiff₁₂ : y₂ / a = y₁ / a + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₁ hy₂ h₁₂
      hy₁β hy₂β hgap hclose₁₂
  have hdiff₁₃ : y₃ / b = y₁ / b + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₁ hy₃ (h₁₂.trans h₂₃)
      hy₁β hy₃β hgap hclose₁₃
  have hdiff₂₃ : y₃ / c = y₂ / c + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₂ hy₃ h₂₃
      hy₂β hy₃β hgap hclose₂₃
  have hy₂eq : y₂ = y₁ + a := by
    calc
      y₂ = (y₂ / a) * a := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₁ y₂)).symm
      _ = (y₁ / a + 1) * a := by rw [hdiff₁₂]
      _ = y₁ + a := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₂)]; simp
  have hy₃eq₁ : y₃ = y₁ + b := by
    calc
      y₃ = (y₃ / b) * b := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₁ y₃)).symm
      _ = (y₁ / b + 1) * b := by rw [hdiff₁₃]
      _ = y₁ + b := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₃)]; simp
  have hy₃eq₂ : y₃ = y₂ + c := by
    calc
      y₃ = (y₃ / c) * c := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₂ y₃)).symm
      _ = (y₂ / c + 1) * c := by rw [hdiff₂₃]
      _ = y₂ + c := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₂ y₃)]; simp
  have habc : a + c = b := by omega
  have hNsplit : δ + β = N := Nat.sub_add_cancel hβN.le
  have hβb : β * b < δ * y₁ := by
    have hbase : β < δ * (y₁ / b) := by
      change β * (y₃ / b) < N * (y₁ / b) at hclose₁₃
      rw [hdiff₁₃] at hclose₁₃
      rw [← hNsplit, add_mul, mul_add] at hclose₁₃
      omega
    have hm := (Nat.mul_lt_mul_right hb).mpr hbase
    calc
      β * b < (δ * (y₁ / b)) * b := hm
      _ = δ * ((y₁ / b) * b) := by rw [mul_assoc]
      _ = δ * y₁ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₃)]
  have hNb : N * b < δ * y₃ := by
    calc
      N * b = (β + δ) * b := by rw [add_comm, hNsplit]
      _ = β * b + δ * b := by rw [add_mul]
      _ < δ * y₁ + δ * b := Nat.add_lt_add_right hβb _
      _ = δ * y₃ := by rw [hy₃eq₁, mul_add]
  have hNbmid : N * b < δ * y₂ + δ * c := by
    simpa only [hy₃eq₂, mul_add] using hNb
  have hprodDvd : y₁ * y₂ * y₃ ∣ β * a * b * c := by
    exact triple_product_dvd_mul_pairwise_gcds hβ hy₁ hy₂ hy₃
      hy₁β hy₂β hy₃β hgcd
  have hprodLe : y₁ * y₂ * y₃ ≤ β * a * b * c :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hβ ha) hb) hc) hprodDvd
  let P := (β * b) * (N * b)
  have hP : 0 < P := by positivity
  have hpair : P < (δ * y₁) * (δ * y₃) := by
    exact mul_lt_mul hβb hNb.le (Nat.mul_pos (by omega) hb)
      (Nat.zero_le (δ * y₁))
  have hpairY₂ : P * (δ * y₂) <
      ((δ * y₁) * (δ * y₃)) * (δ * y₂) := by
    exact (Nat.mul_lt_mul_right (Nat.mul_pos hδ hy₂)).mpr hpair
  have hlarge : P * (N * b) <
      (δ * δ * δ) * (y₁ * y₂ * y₃) + P * (δ * c) := by
    calc
      P * (N * b) < P * (δ * y₂ + δ * c) :=
        (Nat.mul_lt_mul_left hP).mpr hNbmid
      _ = P * (δ * y₂) + P * (δ * c) := by rw [mul_add]
      _ < ((δ * y₁) * (δ * y₃)) * (δ * y₂) + P * (δ * c) :=
        Nat.add_lt_add_right hpairY₂ _
      _ = (δ * δ * δ) * (y₁ * y₂ * y₃) + P * (δ * c) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
  have hlarge' : P * (N * b) <
      (δ * δ * δ) * (β * a * b * c) + P * (δ * c) :=
    hlarge.trans_le (Nat.add_le_add_right
      (Nat.mul_le_mul_left (δ * δ * δ) hprodLe) _)
  have hmain : (b * N) * (b * N) <
      (a * c * δ) * (δ * δ) + (b * N) * (c * δ) := by
    apply (Nat.mul_lt_mul_left (Nat.mul_pos hβ hb)).mp
    calc
      (β * b) * ((b * N) * (b * N)) = P * (N * b) := by
        simp only [P]
        ring
      _ < (δ * δ * δ) * (β * a * b * c) + P * (δ * c) := hlarge'
      _ = (β * b) *
          ((a * c * δ) * (δ * δ) + (b * N) * (c * δ)) := by
        simp only [P]
        ring
  exact spacing_polynomial_contradiction hN hδ ha hc habc hgap hmain

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma exists_increasing_permutation {x y z : ℕ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c, a < b ∧ b < c ∧ ({a, b, c} : Finset ℕ) = {x, y, z} := by
  by_cases h₁ : x < y
  · by_cases h₂ : y < z
    · exact ⟨x, y, z, h₁, h₂, rfl⟩
    · by_cases h₃ : x < z
      · refine ⟨x, z, y, h₃, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨z, x, y, by omega, h₁, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
  · by_cases h₂ : x < z
    · refine ⟨y, x, z, by omega, h₂, ?_⟩
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · by_cases h₃ : y < z
      · refine ⟨y, z, x, h₃, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨z, y, x, by omega, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representationCount_le_two_of_gaps (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hα : 0 < α) (hαN : α ≤ A.card)
    (hαp : α < p) (hβN : p - α < A.card)
    (hsq : A.card * A.card < 2 * (α * α))
    (hgapα : (A.card - α) * (A.card - α) < α)
    (hgapβ : (A.card - (p - α)) * (A.card - (p - α)) ≤ 4 * A.card) :
    representationCount A p α ≤ 2 := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  change R.card ≤ 2
  by_contra hcard
  have hthree : 2 < R.card := by omega
  obtain ⟨x, hxR, y, hyR, z, hzR, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  obtain ⟨e₁, e₂, e₃, he₁₂, he₂₃, hperm⟩ :=
    exists_increasing_permutation hxy hxz hyz
  have hsub : ({e₁, e₂, e₃} : Finset ℕ) ⊆ R := by
    rw [hperm]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxR, hyR, hzR⟩
  have he₁R : e₁ ∈ R := hsub (by simp)
  have he₂R : e₂ ∈ R := hsub (by simp)
  have he₃R : e₃ ∈ R := hsub (by simp)
  have he₁data := (mem_representedMultipliers hα).mp he₁R
  have he₂data := (mem_representedMultipliers hα).mp he₂R
  have he₃data := (mem_representedMultipliers hα).mp he₃R
  let S : Finset ℕ := {e₁, e₂, e₃}
  let c := S.gcd id
  have hS₀ : 0 ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨he₁data.1.ne, he₂data.1.ne, he₃data.1.ne⟩
  have hSne : S.Nonempty := ⟨e₁, by simp [S]⟩
  have hc : 0 < c := gcd_pos S hS₀ hSne
  have he₁S : e₁ ∈ S := by simp [S]
  have he₂S : e₂ ∈ S := by simp [S]
  have he₃S : e₃ ∈ S := by simp [S]
  have hce₁ : c ∣ e₁ := Finset.gcd_dvd he₁S
  have hce₂ : c ∣ e₂ := Finset.gcd_dvd he₂S
  have hce₃ : c ∣ e₃ := Finset.gcd_dvd he₃S
  let d₁ := e₁ / c
  let d₂ := e₂ / c
  let d₃ := e₃ / c
  have hd₁ : 0 < d₁ := Nat.div_pos (Nat.le_of_dvd he₁data.1 hce₁) hc
  have hd₂ : 0 < d₂ := Nat.div_pos (Nat.le_of_dvd he₂data.1 hce₂) hc
  have hd₃ : 0 < d₃ := Nat.div_pos (Nat.le_of_dvd he₃data.1 hce₃) hc
  have hd₁₂ : d₁ < d₂ :=
    (Nat.div_lt_div_right hc.ne' hce₁ hce₂).mpr he₁₂
  have hd₂₃ : d₂ < d₃ :=
    (Nat.div_lt_div_right hc.ne' hce₂ hce₃).mpr he₂₃
  have hd₁c : d₁ * c = e₁ := Nat.div_mul_cancel hce₁
  have hd₂c : d₂ * c = e₂ := Nat.div_mul_cancel hce₂
  have hd₃c : d₃ * c = e₃ := Nat.div_mul_cancel hce₃
  have hRne : R.Nonempty := ⟨e₁, he₁R⟩
  have hRgcd_c : R.gcd id ∣ c := by
    apply Finset.dvd_gcd
    intro e heS
    exact Finset.gcd_dvd (hsub heS)
  have hdvd : ∀ i ∈ ({d₁, d₂, d₃} : Finset ℕ), i ∣ α * β := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (Nat.div_dvd_div_left hce₁ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₁ / R.gcd id) (normalize_mem R he₁R))
    · exact (Nat.div_dvd_div_left hce₂ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₂ / R.gcd id) (normalize_mem R he₂R))
    · exact (Nat.div_dvd_div_left hce₃ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₃ / R.gcd id) (normalize_mem R he₃R))
  have hfac : ∀ i ∈ ({d₁, d₂, d₃} : Finset ℕ),
      i = i.gcd α * i.gcd β := by
    intro i hi
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd i hi)).symm
  have hfac₁ := hfac d₁ (by simp)
  have hfac₂ := hfac d₂ (by simp)
  have hfac₃ := hfac d₃ (by simp)
  have hmemα₁ : α * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.1
  have hmemβ₁ : β * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.2
  have hmemα₂ : α * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.1
  have hmemβ₂ : β * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.2
  have hmemα₃ : α * d₃ * c ∈ A := by rw [mul_assoc, hd₃c]; exact he₃data.2.1
  have hmemβ₃ : β * d₃ * c ∈ A := by rw [mul_assoc, hd₃c]; exact he₃data.2.2
  have hclose₁₂ := scaled_component_closeness A hbad hα hβ hd₁ hd₂ hc
    hαβ hsq hfac₁ hfac₂ hmemα₁ hmemβ₁ hmemα₂ hmemβ₂
  have hclose₁₃ := scaled_component_closeness A hbad hα hβ hd₁ hd₃ hc
    hαβ hsq hfac₁ hfac₃ hmemα₁ hmemβ₁ hmemα₃ hmemβ₃
  have hclose₂₃ := scaled_component_closeness A hbad hα hβ hd₂ hd₃ hc
    hαβ hsq hfac₂ hfac₃ hmemα₂ hmemβ₂ hmemα₃ hmemβ₃
  have hX₁₂ : d₁.gcd α = d₂.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₂)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₂ α)
      hgapα hclose₁₂.1 hclose₁₂.2.1
  have hX₁₃ : d₁.gcd α = d₃.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₃)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₃ α)
      hgapα hclose₁₃.1 hclose₁₃.2.1
  have hgcdNorm : d₁.gcd (d₂.gcd d₃) = 1 := by
    have hg := Finset.gcd_div_id_eq_one he₁S he₁data.1.ne'
    change S.gcd (fun e ↦ e / S.gcd id) = 1 at hg
    simpa only [S, c, d₁, d₂, d₃, Finset.gcd_insert,
      Finset.gcd_singleton, id_eq, normalize_eq, gcd_eq_nat_gcd] using hg
  have hXone : d₁.gcd α = 1 := by
    apply Nat.dvd_one.mp
    rw [← hgcdNorm]
    apply Nat.dvd_gcd (Nat.gcd_dvd_left d₁ α)
    apply Nat.dvd_gcd
    · rw [hX₁₂]
      exact Nat.gcd_dvd_left d₂ α
    · rw [hX₁₃]
      exact Nat.gcd_dvd_left d₃ α
  have hX₂one : d₂.gcd α = 1 := hX₁₂.symm.trans hXone
  have hX₃one : d₃.gcd α = 1 := hX₁₃.symm.trans hXone
  have hY₁ : d₁.gcd β = d₁ := by simpa [hXone] using hfac₁.symm
  have hY₂ : d₂.gcd β = d₂ := by simpa [hX₂one] using hfac₂.symm
  have hY₃ : d₃.gcd β = d₃ := by simpa [hX₃one] using hfac₃.symm
  have hd₁β : d₁ ∣ β := hY₁ ▸ Nat.gcd_dvd_right d₁ β
  have hd₂β : d₂ ∣ β := hY₂ ▸ Nat.gcd_dvd_right d₂ β
  have hd₃β : d₃ ∣ β := hY₃ ▸ Nat.gcd_dvd_right d₃ β
  apply no_three_close_divisors hN hβ hβN hd₁ hd₂ hd₃ hd₁₂ hd₂₃
    hd₁β hd₂β hd₃β hgcdNorm hgapβ
  · simpa only [hY₁, hY₂] using hclose₁₂.2.2.2
  · simpa only [hY₁, hY₃] using hclose₁₃.2.2.2
  · simpa only [hY₂, hY₃] using hclose₂₃.2.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representationCount_le_two_of_window (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card) :
    representationCount A p α ≤ 2 := by
  let N := A.card
  let t := 2 * N - p
  obtain ⟨hαlower, hαN⟩ := Finset.mem_Icc.mp hαJ
  have htadd : t + p = 2 * N := Nat.sub_add_cancel hpupper
  have hpN : N < p := by
    nlinarith [sq_nonneg ((t : ℤ) - N)]
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hp2α : p < 2 * α := by
    omega
  have hα : 0 < α := by omega
  have hαp : α < p := hαN.trans_lt hpN
  have hβN : p - α < N := by omega
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  have h2δ : 2 * (N - α) < t := by omega
  have hgapα : (N - α) * (N - α) < α := by
    nlinarith
  have hsq : N * N < 2 * (α * α) := by
    nlinarith [sq_nonneg ((N : ℤ) - 3 * (N - α))]
  have hδβle : N - (p - α) ≤ t := by omega
  have hgapβ : (N - (p - α)) * (N - (p - α)) ≤ 4 * N := by
    exact (Nat.mul_self_le_mul_self hδβle).trans hpwindow
  apply representationCount_le_two_of_gaps A hbad hp hN hα hαN hαp hβN
  · simpa only [N] using hsq
  · simpa only [N] using hgapα
  · simpa only [N] using hgapβ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def primeFold (p q : ℕ) : ℕ := max q (p - q)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma primeFold_injective_on_odd_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : 2 < p) (hq2 : 2 < q) (hr2 : 2 < r)
    (hqp : q ≤ p) (hrp : r ≤ p)
    (hfold : primeFold p q = primeFold p r) : q = r := by
  have hor : q = r ∨ q + r = p := by
    dsimp only [primeFold] at hfold
    by_cases hqside : q ≤ p - q
    · rw [max_eq_right hqside] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        left
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        right
        omega
    · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hqside))] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        right
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        left
        exact hfold
  rcases hor with h | hsum
  · exact h
  · obtain ⟨kp, hkp⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨kq, hkq⟩ := hq.odd_of_ne_two (by omega)
    obtain ⟨kr, hkr⟩ := hr.odd_of_ne_two (by omega)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma primeFold_mem_J {N p q : ℕ} (hpN : N < p) (hpupper : p ≤ 2 * N)
    (hq : q ∈ Finset.Icc (p - N) N) :
    primeFold p q ∈ Finset.Icc ((p + 1) / 2) N := by
  obtain ⟨hqlower, hqupper⟩ := Finset.mem_Icc.mp hq
  have hqp : q ≤ p := hqupper.trans hpN.le
  have hsubupper : p - q ≤ N := by omega
  apply Finset.mem_Icc.mpr
  constructor
  · dsimp only [primeFold]
    omega
  · exact max_le hqupper hsubupper

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma representationCount_primeFold_eq_zero (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p q : ℕ} (hq : q.Prime) (hqp : q ≤ p)
    (hlarge : A.card ≤ 2 * q) :
    representationCount A p (primeFold p q) = 0 := by
  rw [representationCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨d, hd⟩
  have hαpos : 0 < primeFold p q :=
    lt_max_of_lt_left hq.pos
  have hdata := (mem_representedMultipliers hαpos).mp hd
  by_cases hside : q ≤ p - q
  · have hfold : primeFold p q = p - q := max_eq_right hside
    have hcomp : p - primeFold p q = q := by rw [hfold]; omega
    have hmem : q * d ∈ A := by simpa only [hcomp] using hdata.2.2
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)
  · have hfold : primeFold p q = q :=
      max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hside))
    have hmem : q * d ∈ A := by simpa only [hfold] using hdata.2.1
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma primeInterval_card_le_zeroFibers (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p : ℕ} (hp : p.Prime) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q) :
    ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card := by
  classical
  let Q := (Finset.Icc (p - A.card) A.card).filter Nat.Prime
  let Z := (Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    representationCount A p α = 0
  apply Finset.card_le_card_of_injOn (primeFold p)
  · intro q hqQ
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hqprime := (Finset.mem_filter.mp hqQ).2
    apply Finset.mem_filter.mpr
    refine ⟨primeFold_mem_J hpN hpupper.le hqI, ?_⟩
    exact representationCount_primeFold_eq_zero A h₀ hgcd hbad hqprime
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le) (hlower q hqQ)
  · intro q hqQ r hrQ hfold
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hrI := (Finset.mem_filter.mp hrQ).1
    exact primeFold_injective_on_odd_primes hp
      (Finset.mem_filter.mp hqQ).2 (Finset.mem_filter.mp hrQ).2
      (by omega) (hq2 q hqQ) (hq2 r hrQ)
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le)
      ((Finset.mem_Icc.mp hrI).2.trans hpN.le) hfold

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_collision_support_lt_primeInterval (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q)
    (hsupport : ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card) :
    GrahamBound A := by
  by_contra hbad
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hmult : ∀ α ∈ M, representationCount A p α ≤ 2 := by
    intro α hαM
    exact representationCount_le_two_of_window A hbad hp hN hpupper.le hpwindow
      (Finset.mem_filter.mp hαM).1
  have hexcess : M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card := by
    calc
      M.sum (fun α ↦ representationCount A p α - 1) ≤ M.sum (fun _ ↦ 1) := by
        apply Finset.sum_le_sum
        intro α hαM
        have := hmult α hαM
        omega
      _ = M.card := by simp
  have hprimeZero := primeInterval_card_le_zeroFibers A h₀ hgcd hbad hp hpN hpupper
    hlower hq2
  have hzeroExcess := zero_card_le_representation_excess A h₀ hgcd hbad hp hpN hpupper
  change M.card < _ at hsupport
  change _ ≤ (J.filter fun α ↦ 2 ≤ representationCount A p α).sum
    (fun α ↦ representationCount A p α - 1) at hzeroExcess
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card at hexcess
  exact (not_lt_of_ge (hprimeZero.trans (hzeroExcess.trans hexcess))) hsupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma square_lt_twice_of_gap {N α : ℕ} (hN : 10 ≤ N)
    (hα : 0 < α) (hαN : α ≤ N) (hgap : (N - α) * (N - α) < α) :
    N * N < 2 * (α * α) := by
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  nlinarith [sq_nonneg ((N : ℤ) - 3 * (N - α))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma collision_fiber_shape (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hj : j ≤ 3) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card)
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hr : 2 ≤ representationCount A p α) :
    ∃ ell Y : ℕ, 1 ≤ ell ∧ 1 ≤ Y ∧ ell ≤ j ∧
      p - α = ell * Y * (Y + 1) := by
  classical
  let N := A.card
  let β := p - α
  let t := 2 * N - p
  obtain ⟨hαlower, hαN⟩ := Finset.mem_Icc.mp hαJ
  have hwindow4 : t * t ≤ 4 * N := by
    exact hpwindow.trans (Nat.mul_le_mul_right N (by omega))
  have htadd : t + p = 2 * N := Nat.sub_add_cancel hpupper
  have hpN : N < p := by
    nlinarith [sq_nonneg ((t : ℤ) - N)]
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hp2α : p < 2 * α := by omega
  have hα : 0 < α := by omega
  have hαp : α < p := hαN.trans_lt hpN
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hβN : β < N := by omega
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  have h2δ : 2 * (N - α) < t := by omega
  have hgapα : (N - α) * (N - α) < α := by nlinarith
  have hsq : N * N < 2 * (α * α) := by
    exact square_lt_twice_of_gap hN hα hαN hgapα
  have hgapβ : (N - β) * (N - β) ≤ 4 * N := by
    have hle : N - β ≤ t := by omega
    exact (Nat.mul_self_le_mul_self hle).trans hwindow4
  let R := representedMultipliers A α β
  change 2 ≤ R.card at hr
  have hRtwo : 1 < R.card := hr
  obtain ⟨x, hxR, y, hyR, hxy⟩ := Finset.one_lt_card.mp hRtwo
  have hxdata := (mem_representedMultipliers hα).mp hxR
  have hydata := (mem_representedMultipliers hα).mp hyR
  let e₁ := min x y
  let e₂ := max x y
  have he₁R : e₁ ∈ R := by
    change min x y ∈ R
    rcases min_choice x y with h | h <;> rw [h]
    · exact hxR
    · exact hyR
  have he₂R : e₂ ∈ R := by
    change max x y ∈ R
    rcases max_choice x y with h | h <;> rw [h]
    · exact hxR
    · exact hyR
  have he₁data := (mem_representedMultipliers hα).mp he₁R
  have he₂data := (mem_representedMultipliers hα).mp he₂R
  have he₁₂ : e₁ < e₂ := by
    dsimp only [e₁, e₂]
    omega
  let c := e₁.gcd e₂
  let d₁ := e₁ / c
  let d₂ := e₂ / c
  have hc : 0 < c := Nat.gcd_pos_of_pos_left e₂ he₁data.1
  have hd₁ : 0 < d₁ := Nat.div_pos (Nat.gcd_le_left e₂ he₁data.1) hc
  have hd₂ : 0 < d₂ := Nat.div_pos (Nat.gcd_le_right e₁ he₂data.1) hc
  have hd₁₂ : d₁ < d₂ :=
    (Nat.div_lt_div_right hc.ne' (Nat.gcd_dvd_left e₁ e₂)
      (Nat.gcd_dvd_right e₁ e₂)).mpr he₁₂
  have hcop : d₁.Coprime d₂ := Nat.coprime_div_gcd_div_gcd hc
  have hd₁c : d₁ * c = e₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left e₁ e₂)
  have hd₂c : d₂ * c = e₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right e₁ e₂)
  have hmemα₁ : α * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.1
  have hmemβ₁ : β * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.2
  have hmemα₂ : α * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.1
  have hmemβ₂ : β * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.2
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd₁ hd₂ hc
    hαβ hcop hsq hmemα₁ hmemβ₁ hmemα₂ hmemβ₂
  have hXcop : (d₁.gcd α).Coprime (d₂.gcd α) :=
    (hcop.of_dvd_left (Nat.gcd_dvd_left d₁ α)).of_dvd_right
      (Nat.gcd_dvd_left d₂ α)
  have hXeq : d₁.gcd α = d₂.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₂)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₂ α)
      hgapα
      (by simpa only [hXcop.gcd_eq_one, Nat.div_one] using hfac.2.2.1)
      (by simpa only [hXcop.gcd_eq_one, Nat.div_one] using hfac.2.2.2.1)
  have hXone : d₁.gcd α = 1 := by
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    apply Nat.dvd_gcd (Nat.gcd_dvd_left d₁ α)
    rw [hXeq]
    exact Nat.gcd_dvd_left d₂ α
  have hX₂one : d₂.gcd α = 1 := hXeq.symm.trans hXone
  have hY₁ : d₁.gcd β = d₁ := by simpa [hXone] using hfac.1.symm
  have hY₂ : d₂.gcd β = d₂ := by simpa [hX₂one] using hfac.2.1.symm
  have hd₁β : d₁ ∣ β := hY₁ ▸ Nat.gcd_dvd_right d₁ β
  have hd₂β : d₂ ∣ β := hY₂ ▸ Nat.gcd_dvd_right d₂ β
  have hdiff : d₂ = d₁ + 1 := by
    have h := reduced_divisors_diff_eq_one hβ hβN.le hd₁ hd₂ hd₁₂
      hd₁β hd₂β hgapβ
      (by simpa only [hY₁, hY₂, hcop.gcd_eq_one, Nat.div_one] using
        hfac.2.2.2.2.2)
    simpa only [hcop.gcd_eq_one, Nat.div_one] using h
  have hprodβ : d₁ * d₂ ∣ β := hcop.mul_dvd_of_dvd_of_dvd hd₁β hd₂β
  let ell := β / (d₁ * d₂)
  have hell : 0 < ell := Nat.div_pos (Nat.le_of_dvd hβ hprodβ)
    (Nat.mul_pos hd₁ hd₂)
  have hβeq : β = ell * d₁ * d₂ := by
    rw [← Nat.div_mul_cancel hprodβ]
    dsimp only [ell]
    ac_rfl
  have hcloseβ : β * d₂ < N * d₁ := by
    simpa only [hY₁, hY₂, N] using hfac.2.2.2.2.2
  let δ := N - β
  have hNsplit : δ + β = N := Nat.sub_add_cancel hβN.le
  have hβδ : β < δ * d₁ := by
    rw [hdiff, mul_add, ← hNsplit, add_mul] at hcloseβ
    omega
  have hellδ : ell * d₂ < δ := by
    apply (Nat.mul_lt_mul_right hd₁).mp
    calc
      ell * d₂ * d₁ = β := by rw [hβeq]; ac_rfl
      _ < δ * d₁ := hβδ
  have hδα : 0 < N - α := by
    have halphaClose : α < N := by
      simpa only [hXone, hX₂one, Nat.mul_one, N] using hfac.2.2.1
    exact Nat.sub_pos_of_lt halphaClose
  have htdecomp : t = (N - α) + δ := by omega
  have hellN : ell * N < t * t := by
    have hpart : ell * β < ell * (δ * d₁) := (Nat.mul_lt_mul_left hell).mpr hβδ
    have hδ : 0 < δ := (Nat.mul_pos hell hd₂).trans hellδ
    calc
      ell * N = ell * δ + ell * β := by rw [← hNsplit, mul_add]
      _ < ell * δ + ell * (δ * d₁) := Nat.add_lt_add_left hpart _
      _ = δ * (ell * d₂) := by rw [hdiff]; simp only [Nat.mul_add]; ac_rfl
      _ < δ * δ := (Nat.mul_lt_mul_left hδ).mpr hellδ
      _ < t * t := Nat.mul_self_lt_mul_self (by omega)
  have hellj : ell ≤ j := by
    have : ell * N < (j + 1) * N := hellN.trans_le hpwindow
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right (by omega : 0 < N)).mp this)
  refine ⟨ell, d₁, hell, hd₁, hellj, ?_⟩
  simpa only [β, hdiff] using hβeq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def collisionShapes (N p j : ℕ) : Finset ℕ :=
  Finset.Icc ((p + 1) / 2) N ∩
    (Finset.Icc 1 j).biUnion fun ell ↦
      (Finset.Icc 1 p.sqrt).image fun Y ↦ p - ell * Y * (Y + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma collision_support_subset_shapes (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hj : j ≤ 3) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).filter
        (fun α ↦ 2 ≤ representationCount A p α) ⊆
      collisionShapes A.card p j := by
  intro α hα
  obtain ⟨hαJ, hr⟩ := Finset.mem_filter.mp hα
  obtain ⟨ell, Y, hell, hY, hellj, hshape⟩ :=
    collision_fiber_shape A hbad hp hN hj hpupper hpwindow hαJ hr
  apply Finset.mem_inter.mpr
  refine ⟨hαJ, Finset.mem_biUnion.mpr ⟨ell,
    Finset.mem_Icc.mpr ⟨hell, hellj⟩, ?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨Y, Finset.mem_Icc.mpr ⟨hY, ?_⟩, ?_⟩
  · apply Nat.le_sqrt.mpr
    calc
      Y * Y ≤ Y * (ell * (Y + 1)) := Nat.mul_le_mul_left Y
        ((Nat.le_succ Y).trans (Nat.le_mul_of_pos_left (Y + 1) hell))
      _ = ell * Y * (Y + 1) := by ac_rfl
      _ = p - α := hshape.symm
      _ ≤ p := Nat.sub_le p α
  · have hprod : 0 < ell * Y * (Y + 1) := Nat.mul_pos (Nat.mul_pos hell hY) (by omega)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_shape_certificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hj : j ≤ 3) (hthree : 3 * A.card ≤ 2 * p)
    (hqmin : 3 < p - A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card)
    (hcert : (collisionShapes A.card p j).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card) :
    GrahamBound A := by
  by_contra hbad
  apply hbad
  apply grahamBound_of_collision_support_lt_primeInterval A h₀ hgcd hp hN hpN hpupper
  · exact hpwindow.trans (Nat.mul_le_mul_right A.card (by omega))
  · intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · exact (Finset.card_le_card
      (collision_support_subset_shapes A hbad hp hN hj hpupper.le hpwindow)).trans_lt hcert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_short_prime_pair (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hN : 10 ≤ A.card)
    {p q : ℕ} (hp : p.Prime) (hpN : A.card < p)
    (hpupper : p < 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ A.card)
    (hq : q.Prime) (hqlower : p - A.card ≤ q) (hqupper : q ≤ A.card) :
    GrahamBound A := by
  apply grahamBound_of_shape_certificate A h₀ hgcd hp hN hpN hpupper
      (j := 0)
  · norm_num
  · have htadd : 2 * A.card - p + p = 2 * A.card :=
      Nat.sub_add_cancel hpupper.le
    have hsplit : p - A.card + (2 * A.card - p) = A.card := by
      omega
    nlinarith
  · have htadd : 2 * A.card - p + p = 2 * A.card :=
      Nat.sub_add_cancel hpupper.le
    have hsplit : p - A.card + (2 * A.card - p) = A.card := by
      omega
    nlinarith
  · simpa using hpwindow
  · have hqmem : q ∈
        (Finset.Icc (p - A.card) A.card).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqlower, hqupper⟩, hq⟩
    have hprimepos : 0 <
        ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card :=
      Finset.card_pos.mpr ⟨q, hqmem⟩
    have hshapezero : (collisionShapes A.card p 0).card = 0 := by
      simp [collisionShapes]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def componentClose (N α β d e : ℕ) : Prop :=
  α * (d.gcd α / (d.gcd α).gcd (e.gcd α)) <
      N * (e.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
  α * (e.gcd α / (d.gcd α).gcd (e.gcd α)) <
      N * (d.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
  β * (d.gcd β / (d.gcd β).gcd (e.gcd β)) <
      N * (e.gcd β / (d.gcd β).gcd (e.gcd β)) ∧
  β * (e.gcd β / (d.gcd β).gcd (e.gcd β)) <
      N * (d.gcd β / (d.gcd β).gcd (e.gcd β))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def pairConfiguration (N α β d e : ℕ) : Prop :=
  0 < d ∧ d < e ∧
  d = d.gcd α * d.gcd β ∧ e = e.gcd α * e.gcd β ∧
  componentClose N α β d e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def tripleConfiguration (N α β d₁ d₂ d₃ : ℕ) : Prop :=
  0 < d₁ ∧ d₁ < d₂ ∧ d₂ < d₃ ∧
  d₁ = d₁.gcd α * d₁.gcd β ∧
  d₂ = d₂.gcd α * d₂.gcd β ∧
  d₃ = d₃.gcd α * d₃.gcd β ∧
  componentClose N α β d₁ d₂ ∧
  componentClose N α β d₁ d₃ ∧
  componentClose N α β d₂ d₃

private instance instDecidablePairConfiguration (N α β d e : ℕ) :
    Decidable (pairConfiguration N α β d e) := by
  unfold pairConfiguration componentClose
  infer_instance

private instance instDecidableTripleConfiguration (N α β d₁ d₂ d₃ : ℕ) :
    Decidable (tripleConfiguration N α β d₁ d₂ d₃) := by
  unfold tripleConfiguration componentClose
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possiblePair (N α β : ℕ) : Bool :=
  decide (∃ d ∈ Nat.divisors (α*β), ∃ e ∈ Nat.divisors (α*β),
    pairConfiguration N α β d e)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possibleTriple (N α β : ℕ) : Bool :=
  decide (∃ d₁ ∈ Nat.divisors (α*β), ∃ d₂ ∈ Nat.divisors (α*β),
    ∃ d₃ ∈ Nat.divisors (α*β), tripleConfiguration N α β d₁ d₂ d₃)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possiblePair_eq_true {N α β : ℕ} :
    possiblePair N α β = true ↔
      ∃ d ∈ Nat.divisors (α*β), ∃ e ∈ Nat.divisors (α*β),
        pairConfiguration N α β d e := by simp [possiblePair]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possibleTriple_eq_true {N α β : ℕ} :
    possibleTriple N α β = true ↔
      ∃ d₁ ∈ Nat.divisors (α*β), ∃ d₂ ∈ Nat.divisors (α*β),
        ∃ d₃ ∈ Nat.divisors (α*β), tripleConfiguration N α β d₁ d₂ d₃ := by
  simp [possibleTriple]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possiblePairAlphas (N p : ℕ) : Finset ℕ :=
  (Finset.Icc ((p + 1) / 2) N).filter fun α ↦
    possiblePair N α (p - α) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private def possibleTripleAlphas (N p : ℕ) : Finset ℕ :=
  (Finset.Icc ((p + 1) / 2) N).filter fun α ↦
    possibleTriple N α (p - α) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma normalized_multiplier_data (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α d : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hR : (representedMultipliers A α (p - α)).Nonempty)
    (hd : d ∈ normalize (representedMultipliers A α (p - α))) :
    0 < d ∧ d ∣ α * (p - α) ∧
      d = d.gcd α * d.gcd (p - α) ∧
      α * d * (representedMultipliers A α (p - α)).gcd id ∈ A ∧
      (p - α) * d * (representedMultipliers A α (p - α)).gcd id ∈ A := by
  let β := p - α
  let R := representedMultipliers A α β
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun hz ↦
    normalize_nonzero R hR₀ (hz ▸ hd)
  have hdvd : d ∣ α * β :=
    normalize_represented_dvd_product A hbad hα hβ hαβ hsq hR d hd
  have hfac : d = d.gcd α * d.gcd β :=
    ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr hdvd).symm
  change d ∈ R.image (fun e ↦ e / R.gcd id) at hd
  obtain ⟨e, heR, rfl⟩ := Finset.mem_image.mp hd
  have hedata := (mem_representedMultipliers hα).mp heR
  have hce : R.gcd id ∣ e := Finset.gcd_dvd heR
  have heq : e / R.gcd id * R.gcd id = e := Nat.div_mul_cancel hce
  refine ⟨hdpos, hdvd, hfac, ?_, ?_⟩
  · change α * (e / R.gcd id) * R.gcd id ∈ A
    rw [mul_assoc, heq]
    exact hedata.2.1
  · change β * (e / R.gcd id) * R.gcd id ∈ A
    rw [mul_assoc, heq]
    exact hedata.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possiblePair_of_collision (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hr : 2 ≤ representationCount A p α) :
    possiblePair A.card α (p - α) = true := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  change 2 ≤ R.card at hr
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hBtwo : 1 < B.card := by
    change 1 < (normalize R).card
    rw [normalize_card]
    omega
  obtain ⟨x, hxB, y, hyB, hxy⟩ := Finset.one_lt_card.mp hBtwo
  let d := min x y
  let e := max x y
  have hdB : d ∈ B := by
    change min x y ∈ B
    rcases min_choice x y with h | h <;> rw [h]
    · exact hxB
    · exact hyB
  have heB : e ∈ B := by
    change max x y ∈ B
    rcases max_choice x y with h | h <;> rw [h]
    · exact hxB
    · exact hyB
  have hde : d < e := by dsimp only [d, e]; omega
  have hddata := normalized_multiplier_data A hbad hp hα hαp hsq hR hdB
  have hedata := normalized_multiplier_data A hbad hp hα hαp hsq hR heB
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hclose := scaled_component_closeness A hbad hα hβ hddata.1 hedata.1 hc
    hαβ hsq hddata.2.2.1 hedata.2.2.1
    hddata.2.2.2.1 hddata.2.2.2.2 hedata.2.2.2.1 hedata.2.2.2.2
  rw [possiblePair_eq_true]
  refine ⟨d, Nat.mem_divisors.mpr ⟨hddata.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    e, Nat.mem_divisors.mpr ⟨hedata.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩, ?_⟩
  exact ⟨hddata.1, hde, hddata.2.2.1, hedata.2.2.1, hclose⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma possibleTriple_of_three_representations (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hr : 3 ≤ representationCount A p α) :
    possibleTriple A.card α (p - α) = true := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  change 3 ≤ R.card at hr
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hBthree : 2 < B.card := by
    change 2 < (normalize R).card
    rw [normalize_card]
    omega
  obtain ⟨x, hxB, y, hyB, z, hzB, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hBthree
  obtain ⟨d₁, d₂, d₃, hd₁₂, hd₂₃, hperm⟩ :=
    exists_increasing_permutation hxy hxz hyz
  have hsub : ({d₁, d₂, d₃} : Finset ℕ) ⊆ B := by
    rw [hperm]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxB, hyB, hzB⟩
  have hd₁B : d₁ ∈ B := hsub (by simp)
  have hd₂B : d₂ ∈ B := hsub (by simp)
  have hd₃B : d₃ ∈ B := hsub (by simp)
  have hd₁data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₁B
  have hd₂data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₂B
  have hd₃data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₃B
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hclose₁₂ := scaled_component_closeness A hbad hα hβ
    hd₁data.1 hd₂data.1 hc hαβ hsq hd₁data.2.2.1 hd₂data.2.2.1
    hd₁data.2.2.2.1 hd₁data.2.2.2.2 hd₂data.2.2.2.1 hd₂data.2.2.2.2
  have hclose₁₃ := scaled_component_closeness A hbad hα hβ
    hd₁data.1 hd₃data.1 hc hαβ hsq hd₁data.2.2.1 hd₃data.2.2.1
    hd₁data.2.2.2.1 hd₁data.2.2.2.2 hd₃data.2.2.2.1 hd₃data.2.2.2.2
  have hclose₂₃ := scaled_component_closeness A hbad hα hβ
    hd₂data.1 hd₃data.1 hc hαβ hsq hd₂data.2.2.1 hd₃data.2.2.1
    hd₂data.2.2.2.1 hd₂data.2.2.2.2 hd₃data.2.2.2.1 hd₃data.2.2.2.2
  rw [possibleTriple_eq_true]
  refine ⟨d₁, Nat.mem_divisors.mpr
      ⟨hd₁data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    d₂, Nat.mem_divisors.mpr
      ⟨hd₂data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    d₃, Nat.mem_divisors.mpr
      ⟨hd₃data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩, ?_⟩
  exact ⟨hd₁data.1, hd₁₂, hd₂₃,
    hd₁data.2.2.1, hd₂data.2.2.1, hd₃data.2.2.1,
    hclose₁₂, hclose₁₃, hclose₂₃⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_configuration_certificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p : ℕ} (hp : p.Prime)
    (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hthree : 3 * A.card ≤ 2 * p) (hqmin : 3 < p - A.card)
    (hsq : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      A.card * A.card < 2 * (α * α))
    (hpair : (possiblePairAlphas A.card p).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card)
    (htriple : possibleTripleAlphas A.card p = ∅) :
    GrahamBound A := by
  by_contra hbad
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hmult : ∀ α ∈ M, representationCount A p α ≤ 2 := by
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    by_contra hnot
    have hr : 3 ≤ representationCount A p α := by omega
    have hαpos : 0 < α := by
      have := (Finset.mem_Icc.mp hαJ).1
      omega
    have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
    have hpossible := possibleTriple_of_three_representations A hbad hp
      hαpos hαp (hsq α hαJ) hr
    have hmem : α ∈ possibleTripleAlphas A.card p :=
      Finset.mem_filter.mpr ⟨hαJ, hpossible⟩
    rw [htriple] at hmem
    exact Finset.notMem_empty α hmem
  have hsupport : M.card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card := by
    apply (Finset.card_le_card ?_).trans_lt hpair
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    have hr := (Finset.mem_filter.mp hαM).2
    have hαpos : 0 < α := by
      have := (Finset.mem_Icc.mp hαJ).1
      omega
    have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
    apply Finset.mem_filter.mpr
    exact ⟨hαJ, possiblePair_of_collision A hbad hp hαpos hαp (hsq α hαJ) hr⟩
  have hexcess : M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card := by
    calc
      M.sum (fun α ↦ representationCount A p α - 1) ≤ M.sum (fun _ ↦ 1) := by
        apply Finset.sum_le_sum
        intro α hαM
        have := hmult α hαM
        omega
      _ = M.card := by simp
  have hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hprimeZero := primeInterval_card_le_zeroFibers A h₀ hgcd hbad hp hpN hpupper
    hlower hq2
  have hzeroExcess := zero_card_le_representation_excess A h₀ hgcd hbad hp hpN hpupper
  change M.card < _ at hsupport
  change _ ≤ (J.filter fun α ↦ 2 ≤ representationCount A p α).sum
    (fun α ↦ representationCount A p α - 1) at hzeroExcess
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card at hexcess
  exact (not_lt_of_ge (hprimeZero.trans (hzeroExcess.trans hexcess))) hsupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_27 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card = 27) : GrahamBound A := by
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 27 := (normalize_card A).trans hcard
  apply grahamBound_of_configuration_certificate B hB₀ hBgcd (p := 43)
      (by decide +kernel) (by omega) (by omega) (by omega) (by omega)
  · intro α hα
    have hlo := (Finset.mem_Icc.mp hα).1
    have hs := Nat.mul_self_le_mul_self hlo
    norm_num [hBcard] at hs ⊢
    omega
  · simpa only [hBcard] using (show
      (possiblePairAlphas 27 43).card <
        ((Finset.Icc (43 - 27) 27).filter Nat.Prime).card by decide +kernel)
  · simpa only [hBcard] using (show
      possibleTripleAlphas 27 43 = ∅ by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_65 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card = 65) : GrahamBound A := by
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 65 := (normalize_card A).trans hcard
  apply grahamBound_of_configuration_certificate B hB₀ hBgcd (p := 113)
      (by decide +kernel) (by omega) (by omega) (by omega) (by omega)
  · intro α hα
    have hlo := (Finset.mem_Icc.mp hα).1
    have hs := Nat.mul_self_le_mul_self hlo
    norm_num [hBcard] at hs ⊢
    omega
  · simpa only [hBcard] using (show
      (possiblePairAlphas 65 113).card <
        ((Finset.Icc (113 - 65) 65).filter Nat.Prime).card by decide +kernel)
  · simpa only [hBcard] using (show
      possibleTripleAlphas 65 113 = ∅ by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma dvd_lcm_Ico_of_not_grahamBound (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {a : ℕ} (ha : a ∈ A) :
    a ∣ (Finset.Ico 1 A.card).lcm id := by
  classical
  have ha0 : a ≠ 0 := fun h ↦ h₀ (h ▸ ha)
  have hquot : ∀ b ∈ A, a / a.gcd b ∈ Finset.Ico 1 A.card := by
    intro b hb
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hqpos : 0 < a / a.gcd b :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hlt : a / a.gcd b < A.card := by
      rw [Nat.div_lt_iff_lt_mul hgpos]
      exact Nat.lt_of_not_ge fun hle ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using hle⟩
    exact Finset.mem_Ico.mpr ⟨hqpos, hlt⟩
  have hlcm : A.lcm (fun b ↦ a / a.gcd b) ∣ (Finset.Ico 1 A.card).lcm id :=
    Finset.lcm_dvd fun b hb ↦ Finset.dvd_lcm (hquot b hb)
  rw [lcm_div_gcd_eq a ha0 A, hgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_four (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 4) : GrahamBound A := by
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = A.card := normalize_card A
  have hBne : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    exact Finset.card_pos.mpr hA
  have hdvd : ∀ b ∈ B, b ∣ (Finset.Ico 1 B.card).lcm id :=
    fun b hb ↦ dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
  have hBcard_le : B.card ≤ 4 := hBcard.trans_le hcard
  have hBcard_pos : 0 < B.card := Finset.card_pos.mpr hBne
  rcases (show B.card = 1 ∨ B.card = 2 ∨ B.card = 3 ∨ B.card = 4 by omega) with
    h₁ | h₂ | h₃ | h₄
  · obtain ⟨a, ha⟩ := hBne
    apply hbad
    refine ⟨a, ha, a, ha, ?_⟩
    simp [h₁]
  · have hsub : B ⊆ Nat.divisors 1 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      simpa [h₂] using hdvd b hb
    have hle := Finset.card_le_card hsub
    rw [h₂, Nat.divisors_one, Finset.card_singleton] at hle
    omega
  · have hsub : B ⊆ Nat.divisors 2 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      have hbdiv := hdvd b hb
      rw [h₃, show (Finset.Ico 1 3).lcm id = 2 by decide +kernel] at hbdiv
      exact hbdiv
    have hle := Finset.card_le_card hsub
    rw [h₃] at hle
    have hdivcard : (Nat.divisors 2).card = 2 := by decide +kernel
    rw [hdivcard] at hle
    omega
  · have hsub : B ⊆ Nat.divisors 6 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      have hbdiv := hdvd b hb
      rw [h₄, show (Finset.Ico 1 4).lcm id = 6 by decide +kernel] at hbdiv
      exact hbdiv
    have heq : B = Nat.divisors 6 := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [h₄]
      decide
    have h6 : 6 ∈ B := heq ▸ by norm_num
    have h1 : 1 ∈ B := heq ▸ by norm_num
    apply hbad
    exact ⟨6, h6, 1, h1, by norm_num [h₄]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_lcm_certificate (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) {n L : ℕ} (hcard : A.card = n) (hL₀ : L ≠ 0)
    (hlcm : (Finset.Ico 1 n).lcm id = L)
    (hcert : badSubsets (Nat.divisors L) n = ∅) : GrahamBound A := by
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcardA : B.card = A.card := normalize_card A
  have hBcard : B.card = n := hBcardA.trans hcard
  have hsub : B ⊆ Nat.divisors L := by
    intro b hb
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hL₀⟩
    have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
    simpa [hBcard, hlcm] using hdvd
  exact hbad (grahamBound_of_badSubsets_eq_empty hcert hsub hBcard)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_seven (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 7) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 4
  · exact grahamBound_of_card_le_four A h₀ hA hsmall
  have hpos : 0 < A.card := Finset.card_pos.mpr hA
  rcases (show A.card = 5 ∨ A.card = 6 ∨ A.card = 7 by omega) with h₅ | h₆ | h₇
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 5) (L := 12) h₅ (by norm_num)
      (by decide +kernel)
    decide +kernel
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 6) (L := 60) h₆ (by norm_num)
      (by decide +kernel)
    decide +kernel
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 7) (L := 60) h₇ (by norm_num)
      (by decide +kernel)
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_eight (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 8) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 7
  · exact grahamBound_of_card_le_seven A h₀ hA hsmall
  have hcard8 : A.card = 8 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 8 := (normalize_card A).trans hcard8
  let T := (Nat.divisors 420).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 8).lcm id = 420 by decide +kernel] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by decide +kernel) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by decide +kernel) (by norm_num [hBcard]) hb
  have hle := Finset.card_le_card hsub
  have hTcard : T.card = 6 := by decide +kernel
  rw [hBcard, hTcard] at hle
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_nine (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 9) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 8
  · exact grahamBound_of_card_le_eight A h₀ hA hsmall
  have hcard9 : A.card = 9 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 9 := (normalize_card A).trans hcard9
  let T := (Nat.divisors 840).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 9).lcm id = 840 by decide +kernel] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by decide +kernel) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by decide +kernel) (by norm_num [hBcard]) hb
  have hle := Finset.card_le_card hsub
  have hTcard : T.card = 8 := by decide +kernel
  rw [hBcard, hTcard] at hle
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma grahamBound_of_card_le_ten (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 10) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 9
  · exact grahamBound_of_card_le_nine A h₀ hA hsmall
  have hcard10 : A.card = 10 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 10 := (normalize_card A).trans hcard10
  let T := (Nat.divisors 2520).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 10).lcm id = 2520 by decide +kernel] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by decide +kernel) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by decide +kernel) (by norm_num [hBcard]) hb
  have hcert : badSubsets T 10 = ∅ := by decide +kernel
  exact hbad (grahamBound_of_badSubsets_eq_empty hcert hsub hBcard)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma pair_block (lo hi p q : ℕ)
    (hlo10 : 10 ≤ lo) (hp : p.Prime) (hpN : hi < p)
    (hupper : p < 2*lo) (hwin : (2*hi-p)*(2*hi-p) ≤ lo)
    (hq : q.Prime) (hql : p-lo ≤ q) (hqu : q ≤ lo)
    (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : lo ≤ A.card) (hhi : A.card ≤ hi) : GrahamBound A := by
  apply grahamBound_of_short_prime_pair A h0 hg (by omega) hp (by omega) (by omega)
  · have hsub : 2*A.card-p ≤ 2*hi-p := Nat.sub_le_sub_right (by omega) p
    exact (Nat.mul_self_le_mul_self hsub).trans (hwin.trans hlo)
  · exact hq
  · omega
  · omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_0 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 11 ≤ A.card) (hhi : A.card ≤ 11) : GrahamBound A := by
  exact pair_block 11 11 19 11 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_1 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 12 ≤ A.card) (hhi : A.card ≤ 13) : GrahamBound A := by
  exact pair_block 12 13 23 11 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_2 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 14 ≤ A.card) (hhi : A.card ≤ 14) : GrahamBound A := by
  have hn : A.card = 14 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=23) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_3 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 15 ≤ A.card) (hhi : A.card ≤ 15) : GrahamBound A := by
  have hn : A.card = 15 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=23) (j:=3)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_4 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 16 ≤ A.card) (hhi : A.card ≤ 16) : GrahamBound A := by
  exact pair_block 16 16 29 13 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_5 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 17 ≤ A.card) (hhi : A.card ≤ 17) : GrahamBound A := by
  exact pair_block 17 17 31 17 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_6 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 18 ≤ A.card) (hhi : A.card ≤ 18) : GrahamBound A := by
  have hn : A.card = 18 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=31) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_7 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 19 ≤ A.card) (hhi : A.card ≤ 20) : GrahamBound A := by
  exact pair_block 19 20 37 19 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_8 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 21 ≤ A.card) (hhi : A.card ≤ 21) : GrahamBound A := by
  have hn : A.card = 21 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=37) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_9 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 22 ≤ A.card) (hhi : A.card ≤ 22) : GrahamBound A := by
  exact pair_block 22 22 41 19 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_10 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 23 ≤ A.card) (hhi : A.card ≤ 23) : GrahamBound A := by
  exact pair_block 23 23 43 23 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_11 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 24 ≤ A.card) (hhi : A.card ≤ 25) : GrahamBound A := by
  exact pair_block 24 25 47 23 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_12 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 26 ≤ A.card) (hhi : A.card ≤ 26) : GrahamBound A := by
  exact pair_block 26 26 47 23 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_13 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 27 ≤ A.card) (hhi : A.card ≤ 27) : GrahamBound A := by
  exact grahamBound_of_card_27 A h0 (Finset.card_pos.mp (by omega)) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_14 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 28 ≤ A.card) (hhi : A.card ≤ 28) : GrahamBound A := by
  have hn : A.card = 28 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=47) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_15 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 29 ≤ A.card) (hhi : A.card ≤ 29) : GrahamBound A := by
  exact pair_block 29 29 53 29 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_16 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 30 ≤ A.card) (hhi : A.card ≤ 32) : GrahamBound A := by
  exact pair_block 30 32 59 29 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_17 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 33 ≤ A.card) (hhi : A.card ≤ 33) : GrahamBound A := by
  exact pair_block 33 33 61 29 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_18 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 34 ≤ A.card) (hhi : A.card ≤ 34) : GrahamBound A := by
  have hn : A.card = 34 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=61) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_19 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 35 ≤ A.card) (hhi : A.card ≤ 35) : GrahamBound A := by
  have hn : A.card = 35 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=61) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_20 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 36 ≤ A.card) (hhi : A.card ≤ 36) : GrahamBound A := by
  exact pair_block 36 36 67 31 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_21 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 37 ≤ A.card) (hhi : A.card ≤ 39) : GrahamBound A := by
  exact pair_block 37 39 73 37 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_22 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 40 ≤ A.card) (hhi : A.card ≤ 40) : GrahamBound A := by
  have hn : A.card = 40 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=73) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_23 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 41 ≤ A.card) (hhi : A.card ≤ 42) : GrahamBound A := by
  exact pair_block 41 42 79 41 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_24 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 43 ≤ A.card) (hhi : A.card ≤ 44) : GrahamBound A := by
  exact pair_block 43 44 83 41 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_25 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 45 ≤ A.card) (hhi : A.card ≤ 45) : GrahamBound A := by
  have hn : A.card = 45 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=83) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_26 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 46 ≤ A.card) (hhi : A.card ≤ 47) : GrahamBound A := by
  exact pair_block 46 47 89 43 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_27 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 48 ≤ A.card) (hhi : A.card ≤ 48) : GrahamBound A := by
  have hn : A.card = 48 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=89) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_28 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 49 ≤ A.card) (hhi : A.card ≤ 49) : GrahamBound A := by
  have hn : A.card = 49 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=89) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_29 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 50 ≤ A.card) (hhi : A.card ≤ 52) : GrahamBound A := by
  exact pair_block 50 52 97 47 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_30 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 53 ≤ A.card) (hhi : A.card ≤ 55) : GrahamBound A := by
  exact pair_block 53 55 103 53 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_31 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 56 ≤ A.card) (hhi : A.card ≤ 58) : GrahamBound A := by
  exact pair_block 56 58 109 53 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_32 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 59 ≤ A.card) (hhi : A.card ≤ 60) : GrahamBound A := by
  exact pair_block 59 60 113 59 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_33 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 61 ≤ A.card) (hhi : A.card ≤ 61) : GrahamBound A := by
  have hn : A.card = 61 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_34 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 62 ≤ A.card) (hhi : A.card ≤ 62) : GrahamBound A := by
  have hn : A.card = 62 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_35 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 63 ≤ A.card) (hhi : A.card ≤ 63) : GrahamBound A := by
  have hn : A.card = 63 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_36 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 64 ≤ A.card) (hhi : A.card ≤ 64) : GrahamBound A := by
  have hn : A.card = 64 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=113) (j:=3)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_37 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 65 ≤ A.card) (hhi : A.card ≤ 65) : GrahamBound A := by
  exact grahamBound_of_card_65 A h0 (Finset.card_pos.mp (by omega)) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_38 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 66 ≤ A.card) (hhi : A.card ≤ 67) : GrahamBound A := by
  exact pair_block 66 67 127 61 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_39 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 68 ≤ A.card) (hhi : A.card ≤ 69) : GrahamBound A := by
  exact pair_block 68 69 131 67 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_40 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 70 ≤ A.card) (hhi : A.card ≤ 72) : GrahamBound A := by
  exact pair_block 70 72 137 67 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_41 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 73 ≤ A.card) (hhi : A.card ≤ 73) : GrahamBound A := by
  exact pair_block 73 73 139 67 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_42 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 74 ≤ A.card) (hhi : A.card ≤ 74) : GrahamBound A := by
  have hn : A.card = 74 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=139) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_43 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 75 ≤ A.card) (hhi : A.card ≤ 75) : GrahamBound A := by
  have hn : A.card = 75 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=139) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_44 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 76 ≤ A.card) (hhi : A.card ≤ 78) : GrahamBound A := by
  exact pair_block 76 78 149 73 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_45 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 79 ≤ A.card) (hhi : A.card ≤ 82) : GrahamBound A := by
  exact pair_block 79 82 157 79 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_46 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 83 ≤ A.card) (hhi : A.card ≤ 86) : GrahamBound A := by
  exact pair_block 83 86 163 83 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_47 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 87 ≤ A.card) (hhi : A.card ≤ 88) : GrahamBound A := by
  exact pair_block 87 88 167 83 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_48 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 89 ≤ A.card) (hhi : A.card ≤ 91) : GrahamBound A := by
  exact pair_block 89 91 173 89 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_49 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 92 ≤ A.card) (hhi : A.card ≤ 95) : GrahamBound A := by
  exact pair_block 92 95 181 89 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_50 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 96 ≤ A.card) (hhi : A.card ≤ 96) : GrahamBound A := by
  have hn : A.card = 96 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=179) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_51 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 97 ≤ A.card) (hhi : A.card ≤ 101) : GrahamBound A := by
  exact pair_block 97 101 193 97 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_52 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 102 ≤ A.card) (hhi : A.card ≤ 104) : GrahamBound A := by
  exact pair_block 102 104 199 97 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_53 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 105 ≤ A.card) (hhi : A.card ≤ 105) : GrahamBound A := by
  have hn : A.card = 105 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=199) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_54 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 106 ≤ A.card) (hhi : A.card ≤ 106) : GrahamBound A := by
  have hn : A.card = 106 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=199) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_55 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 107 ≤ A.card) (hhi : A.card ≤ 110) : GrahamBound A := by
  exact pair_block 107 110 211 107 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_56 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 111 ≤ A.card) (hhi : A.card ≤ 111) : GrahamBound A := by
  have hn : A.card = 111 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=211) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_57 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 112 ≤ A.card) (hhi : A.card ≤ 112) : GrahamBound A := by
  have hn : A.card = 112 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=211) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_58 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 113 ≤ A.card) (hhi : A.card ≤ 116) : GrahamBound A := by
  exact pair_block 113 116 223 113 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_59 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 117 ≤ A.card) (hhi : A.card ≤ 119) : GrahamBound A := by
  exact pair_block 117 119 229 113 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_60 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 120 ≤ A.card) (hhi : A.card ≤ 121) : GrahamBound A := by
  exact pair_block 120 121 233 113 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_61 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 122 ≤ A.card) (hhi : A.card ≤ 122) : GrahamBound A := by
  exact pair_block 122 122 233 113 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_62 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 123 ≤ A.card) (hhi : A.card ≤ 123) : GrahamBound A := by
  have hn : A.card = 123 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=229) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_63 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 124 ≤ A.card) (hhi : A.card ≤ 124) : GrahamBound A := by
  have hn : A.card = 124 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=233) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_64 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 125 ≤ A.card) (hhi : A.card ≤ 125) : GrahamBound A := by
  have hn : A.card = 125 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=229) (j:=3)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_65 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 126 ≤ A.card) (hhi : A.card ≤ 126) : GrahamBound A := by
  have hn : A.card = 126 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=239) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_66 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 127 ≤ A.card) (hhi : A.card ≤ 131) : GrahamBound A := by
  exact pair_block 127 131 251 127 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_67 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 132 ≤ A.card) (hhi : A.card ≤ 137) : GrahamBound A := by
  exact pair_block 132 137 263 131 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_68 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 138 ≤ A.card) (hhi : A.card ≤ 141) : GrahamBound A := by
  exact pair_block 138 141 271 137 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_69 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 142 ≤ A.card) (hhi : A.card ≤ 146) : GrahamBound A := by
  exact pair_block 142 146 281 139 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_70 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 147 ≤ A.card) (hhi : A.card ≤ 147) : GrahamBound A := by
  exact pair_block 147 147 283 137 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_71 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 148 ≤ A.card) (hhi : A.card ≤ 148) : GrahamBound A := by
  have hn : A.card = 148 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=283) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_72 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 149 ≤ A.card) (hhi : A.card ≤ 152) : GrahamBound A := by
  exact pair_block 149 152 293 149 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_73 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 153 ≤ A.card) (hhi : A.card ≤ 153) : GrahamBound A := by
  have hn : A.card = 153 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=293) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_74 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 154 ≤ A.card) (hhi : A.card ≤ 154) : GrahamBound A := by
  have hn : A.card = 154 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=293) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_75 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 155 ≤ A.card) (hhi : A.card ≤ 155) : GrahamBound A := by
  have hn : A.card = 155 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=293) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_76 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 156 ≤ A.card) (hhi : A.card ≤ 159) : GrahamBound A := by
  exact pair_block 156 159 307 151 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_77 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 160 ≤ A.card) (hhi : A.card ≤ 164) : GrahamBound A := by
  exact pair_block 160 164 317 157 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_78 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 165 ≤ A.card) (hhi : A.card ≤ 165) : GrahamBound A := by
  have hn : A.card = 165 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=317) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_79 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 166 ≤ A.card) (hhi : A.card ≤ 166) : GrahamBound A := by
  have hn : A.card = 166 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=317) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_80 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 167 ≤ A.card) (hhi : A.card ≤ 171) : GrahamBound A := by
  exact pair_block 167 171 331 167 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_81 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 172 ≤ A.card) (hhi : A.card ≤ 175) : GrahamBound A := by
  exact pair_block 172 175 337 167 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_82 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 176 ≤ A.card) (hhi : A.card ≤ 181) : GrahamBound A := by
  exact pair_block 176 181 349 173 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_83 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 182 ≤ A.card) (hhi : A.card ≤ 186) : GrahamBound A := by
  exact pair_block 182 186 359 179 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_84 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 187 ≤ A.card) (hhi : A.card ≤ 190) : GrahamBound A := by
  exact pair_block 187 190 367 181 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_85 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 191 ≤ A.card) (hhi : A.card ≤ 196) : GrahamBound A := by
  exact pair_block 191 196 379 191 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_86 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 197 ≤ A.card) (hhi : A.card ≤ 201) : GrahamBound A := by
  exact pair_block 197 201 389 193 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_87 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 202 ≤ A.card) (hhi : A.card ≤ 207) : GrahamBound A := by
  exact pair_block 202 207 401 199 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_88 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 208 ≤ A.card) (hhi : A.card ≤ 208) : GrahamBound A := by
  have hn : A.card = 208 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=401) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_89 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 209 ≤ A.card) (hhi : A.card ≤ 209) : GrahamBound A := by
  have hn : A.card = 209 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=401) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_90 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 210 ≤ A.card) (hhi : A.card ≤ 211) : GrahamBound A := by
  exact pair_block 210 211 409 199 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_91 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 212 ≤ A.card) (hhi : A.card ≤ 217) : GrahamBound A := by
  exact pair_block 212 217 421 211 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_92 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 218 ≤ A.card) (hhi : A.card ≤ 218) : GrahamBound A := by
  have hn : A.card = 218 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=419) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_93 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 219 ≤ A.card) (hhi : A.card ≤ 219) : GrahamBound A := by
  have hn : A.card = 219 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=419) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_94 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 220 ≤ A.card) (hhi : A.card ≤ 222) : GrahamBound A := by
  exact pair_block 220 222 431 211 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_95 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 223 ≤ A.card) (hhi : A.card ≤ 228) : GrahamBound A := by
  exact pair_block 223 228 443 223 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_96 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 229 ≤ A.card) (hhi : A.card ≤ 236) : GrahamBound A := by
  exact pair_block 229 236 457 229 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_97 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 237 ≤ A.card) (hhi : A.card ≤ 241) : GrahamBound A := by
  exact pair_block 237 241 467 233 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_98 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 242 ≤ A.card) (hhi : A.card ≤ 247) : GrahamBound A := by
  exact pair_block 242 247 479 239 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_99 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 248 ≤ A.card) (hhi : A.card ≤ 251) : GrahamBound A := by
  exact pair_block 248 251 487 239 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_100 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 252 ≤ A.card) (hhi : A.card ≤ 259) : GrahamBound A := by
  exact pair_block 252 259 503 251 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_101 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 260 ≤ A.card) (hhi : A.card ≤ 262) : GrahamBound A := by
  exact pair_block 260 262 509 251 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_102 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 263 ≤ A.card) (hhi : A.card ≤ 269) : GrahamBound A := by
  exact pair_block 263 269 523 263 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_103 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 270 ≤ A.card) (hhi : A.card ≤ 270) : GrahamBound A := by
  have hn : A.card = 270 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=523) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_104 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 271 ≤ A.card) (hhi : A.card ≤ 278) : GrahamBound A := by
  exact pair_block 271 278 541 271 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_105 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 279 ≤ A.card) (hhi : A.card ≤ 281) : GrahamBound A := by
  exact pair_block 279 281 547 269 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_106 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 282 ≤ A.card) (hhi : A.card ≤ 289) : GrahamBound A := by
  exact pair_block 282 289 563 281 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_107 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 290 ≤ A.card) (hhi : A.card ≤ 294) : GrahamBound A := by
  exact pair_block 290 294 571 281 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_108 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 295 ≤ A.card) (hhi : A.card ≤ 302) : GrahamBound A := by
  exact pair_block 295 302 587 293 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_109 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 303 ≤ A.card) (hhi : A.card ≤ 305) : GrahamBound A := by
  exact pair_block 303 305 593 293 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_110 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 306 ≤ A.card) (hhi : A.card ≤ 308) : GrahamBound A := by
  exact pair_block 306 308 599 293 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_111 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 309 ≤ A.card) (hhi : A.card ≤ 315) : GrahamBound A := by
  exact pair_block 309 315 613 307 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_112 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 316 ≤ A.card) (hhi : A.card ≤ 318) : GrahamBound A := by
  exact pair_block 316 318 619 307 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_113 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 319 ≤ A.card) (hhi : A.card ≤ 324) : GrahamBound A := by
  exact pair_block 319 324 631 313 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_114 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 325 ≤ A.card) (hhi : A.card ≤ 329) : GrahamBound A := by
  exact pair_block 325 329 641 317 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_115 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 330 ≤ A.card) (hhi : A.card ≤ 332) : GrahamBound A := by
  exact pair_block 330 332 647 317 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_116 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 333 ≤ A.card) (hhi : A.card ≤ 339) : GrahamBound A := by
  exact pair_block 333 339 661 331 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_117 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 340 ≤ A.card) (hhi : A.card ≤ 347) : GrahamBound A := by
  exact pair_block 340 347 677 337 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_118 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 348 ≤ A.card) (hhi : A.card ≤ 354) : GrahamBound A := by
  exact pair_block 348 354 691 347 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_119 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 355 ≤ A.card) (hhi : A.card ≤ 359) : GrahamBound A := by
  exact pair_block 355 359 701 347 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_120 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 360 ≤ A.card) (hhi : A.card ≤ 368) : GrahamBound A := by
  exact pair_block 360 368 719 359 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_121 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 369 ≤ A.card) (hhi : A.card ≤ 376) : GrahamBound A := by
  exact pair_block 369 376 733 367 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_122 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 377 ≤ A.card) (hhi : A.card ≤ 381) : GrahamBound A := by
  exact pair_block 377 381 743 367 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_123 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 382 ≤ A.card) (hhi : A.card ≤ 390) : GrahamBound A := by
  exact pair_block 382 390 761 379 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_124 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 391 ≤ A.card) (hhi : A.card ≤ 396) : GrahamBound A := by
  exact pair_block 391 396 773 383 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_125 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 397 ≤ A.card) (hhi : A.card ≤ 403) : GrahamBound A := by
  exact pair_block 397 403 787 397 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_126 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 404 ≤ A.card) (hhi : A.card ≤ 408) : GrahamBound A := by
  exact pair_block 404 408 797 397 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_127 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 409 ≤ A.card) (hhi : A.card ≤ 415) : GrahamBound A := by
  exact pair_block 409 415 811 409 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_128 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 416 ≤ A.card) (hhi : A.card ≤ 421) : GrahamBound A := by
  exact pair_block 416 421 823 409 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_129 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 422 ≤ A.card) (hhi : A.card ≤ 429) : GrahamBound A := by
  exact pair_block 422 429 839 419 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_130 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 430 ≤ A.card) (hhi : A.card ≤ 430) : GrahamBound A := by
  have hn : A.card = 430 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=839) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_131 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 431 ≤ A.card) (hhi : A.card ≤ 439) : GrahamBound A := by
  exact pair_block 431 439 859 431 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_132 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 440 ≤ A.card) (hhi : A.card ≤ 448) : GrahamBound A := by
  exact pair_block 440 448 877 439 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_133 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 449 ≤ A.card) (hhi : A.card ≤ 454) : GrahamBound A := by
  exact pair_block 449 454 887 439 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_134 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 455 ≤ A.card) (hhi : A.card ≤ 455) : GrahamBound A := by
  have hn : A.card = 455 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=887) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_135 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 456 ≤ A.card) (hhi : A.card ≤ 456) : GrahamBound A := by
  have hn : A.card = 456 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=887) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_136 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 457 ≤ A.card) (hhi : A.card ≤ 466) : GrahamBound A := by
  exact pair_block 457 466 911 457 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_137 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 467 ≤ A.card) (hhi : A.card ≤ 475) : GrahamBound A := by
  exact pair_block 467 475 929 463 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_138 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 476 ≤ A.card) (hhi : A.card ≤ 481) : GrahamBound A := by
  exact pair_block 476 481 941 467 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_139 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 482 ≤ A.card) (hhi : A.card ≤ 487) : GrahamBound A := by
  exact pair_block 482 487 953 479 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_140 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 488 ≤ A.card) (hhi : A.card ≤ 496) : GrahamBound A := by
  exact pair_block 488 496 971 487 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_141 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 497 ≤ A.card) (hhi : A.card ≤ 502) : GrahamBound A := by
  exact pair_block 497 502 983 487 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_142 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 503 ≤ A.card) (hhi : A.card ≤ 509) : GrahamBound A := by
  exact pair_block 503 509 997 499 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_143 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 510 ≤ A.card) (hhi : A.card ≤ 520) : GrahamBound A := by
  exact pair_block 510 520 1019 509 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_144 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 521 ≤ A.card) (hhi : A.card ≤ 530) : GrahamBound A := by
  exact pair_block 521 530 1039 521 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_145 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 531 ≤ A.card) (hhi : A.card ≤ 537) : GrahamBound A := by
  exact pair_block 531 537 1051 521 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_146 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 538 ≤ A.card) (hhi : A.card ≤ 542) : GrahamBound A := by
  exact pair_block 538 542 1061 523 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_147 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 543 ≤ A.card) (hhi : A.card ≤ 546) : GrahamBound A := by
  exact pair_block 543 546 1069 541 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_148 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 547 ≤ A.card) (hhi : A.card ≤ 558) : GrahamBound A := by
  exact pair_block 547 558 1093 547 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_149 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 559 ≤ A.card) (hhi : A.card ≤ 566) : GrahamBound A := by
  exact pair_block 559 566 1109 557 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_150 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 567 ≤ A.card) (hhi : A.card ≤ 576) : GrahamBound A := by
  exact pair_block 567 576 1129 563 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_151 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 577 ≤ A.card) (hhi : A.card ≤ 588) : GrahamBound A := by
  exact pair_block 577 588 1153 577 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_152 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 589 ≤ A.card) (hhi : A.card ≤ 597) : GrahamBound A := by
  exact pair_block 589 597 1171 587 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_153 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 598 ≤ A.card) (hhi : A.card ≤ 605) : GrahamBound A := by
  exact pair_block 598 605 1187 593 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_154 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 606 ≤ A.card) (hhi : A.card ≤ 612) : GrahamBound A := by
  exact pair_block 606 612 1201 599 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_155 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 613 ≤ A.card) (hhi : A.card ≤ 623) : GrahamBound A := by
  exact pair_block 613 623 1223 613 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_156 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 624 ≤ A.card) (hhi : A.card ≤ 630) : GrahamBound A := by
  exact pair_block 624 630 1237 613 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_157 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 631 ≤ A.card) (hhi : A.card ≤ 642) : GrahamBound A := by
  exact pair_block 631 642 1259 631 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_158 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 643 ≤ A.card) (hhi : A.card ≤ 654) : GrahamBound A := by
  exact pair_block 643 654 1283 641 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_159 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 655 ≤ A.card) (hhi : A.card ≤ 666) : GrahamBound A := by
  exact pair_block 655 666 1307 653 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_160 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 667 ≤ A.card) (hhi : A.card ≤ 676) : GrahamBound A := by
  exact pair_block 667 676 1327 661 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_161 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 677 ≤ A.card) (hhi : A.card ≤ 677) : GrahamBound A := by
  have hn : A.card = 677 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_162 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 678 ≤ A.card) (hhi : A.card ≤ 678) : GrahamBound A := by
  have hn : A.card = 678 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_163 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 679 ≤ A.card) (hhi : A.card ≤ 679) : GrahamBound A := by
  have hn : A.card = 679 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_164 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 680 ≤ A.card) (hhi : A.card ≤ 680) : GrahamBound A := by
  have hn : A.card = 680 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_165 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 681 ≤ A.card) (hhi : A.card ≤ 681) : GrahamBound A := by
  have hn : A.card = 681 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_166 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 682 ≤ A.card) (hhi : A.card ≤ 682) : GrahamBound A := by
  have hn : A.card = 682 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1327) (j:=2)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_167 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 683 ≤ A.card) (hhi : A.card ≤ 693) : GrahamBound A := by
  exact pair_block 683 693 1361 683 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_168 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 694 ≤ A.card) (hhi : A.card ≤ 703) : GrahamBound A := by
  exact pair_block 694 703 1381 691 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_169 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 704 ≤ A.card) (hhi : A.card ≤ 712) : GrahamBound A := by
  exact pair_block 704 712 1399 701 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_170 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 713 ≤ A.card) (hhi : A.card ≤ 717) : GrahamBound A := by
  exact pair_block 713 717 1409 701 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_171 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 718 ≤ A.card) (hhi : A.card ≤ 726) : GrahamBound A := by
  exact pair_block 718 726 1427 709 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_172 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 727 ≤ A.card) (hhi : A.card ≤ 739) : GrahamBound A := by
  exact pair_block 727 739 1453 727 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_173 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 740 ≤ A.card) (hhi : A.card ≤ 749) : GrahamBound A := by
  exact pair_block 740 749 1471 733 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_174 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 750 ≤ A.card) (hhi : A.card ≤ 760) : GrahamBound A := by
  exact pair_block 750 760 1493 743 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_175 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 761 ≤ A.card) (hhi : A.card ≤ 769) : GrahamBound A := by
  exact pair_block 761 769 1511 751 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_176 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 770 ≤ A.card) (hhi : A.card ≤ 779) : GrahamBound A := by
  exact pair_block 770 779 1531 761 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_177 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 780 ≤ A.card) (hhi : A.card ≤ 790) : GrahamBound A := by
  exact pair_block 780 790 1553 773 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_178 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 791 ≤ A.card) (hhi : A.card ≤ 799) : GrahamBound A := by
  exact pair_block 791 799 1571 787 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_179 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 800 ≤ A.card) (hhi : A.card ≤ 812) : GrahamBound A := by
  exact pair_block 800 812 1597 797 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_180 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 813 ≤ A.card) (hhi : A.card ≤ 824) : GrahamBound A := by
  exact pair_block 813 824 1621 809 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_181 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 825 ≤ A.card) (hhi : A.card ≤ 832) : GrahamBound A := by
  exact pair_block 825 832 1637 821 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_182 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 833 ≤ A.card) (hhi : A.card ≤ 842) : GrahamBound A := by
  exact pair_block 833 842 1657 827 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_183 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 843 ≤ A.card) (hhi : A.card ≤ 849) : GrahamBound A := by
  exact pair_block 843 849 1669 827 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_184 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 850 ≤ A.card) (hhi : A.card ≤ 850) : GrahamBound A := by
  have hn : A.card = 850 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1669) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_185 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 851 ≤ A.card) (hhi : A.card ≤ 851) : GrahamBound A := by
  have hn : A.card = 851 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1669) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_186 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 852 ≤ A.card) (hhi : A.card ≤ 852) : GrahamBound A := by
  have hn : A.card = 852 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=1669) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_187 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 853 ≤ A.card) (hhi : A.card ≤ 864) : GrahamBound A := by
  exact pair_block 853 864 1699 853 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_188 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 865 ≤ A.card) (hhi : A.card ≤ 876) : GrahamBound A := by
  exact pair_block 865 876 1723 859 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_189 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 877 ≤ A.card) (hhi : A.card ≤ 891) : GrahamBound A := by
  exact pair_block 877 891 1753 877 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_190 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 892 ≤ A.card) (hhi : A.card ≤ 903) : GrahamBound A := by
  exact pair_block 892 903 1777 887 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_191 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 904 ≤ A.card) (hhi : A.card ≤ 909) : GrahamBound A := by
  exact pair_block 904 909 1789 887 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_192 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 910 ≤ A.card) (hhi : A.card ≤ 920) : GrahamBound A := by
  exact pair_block 910 920 1811 907 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_193 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 921 ≤ A.card) (hhi : A.card ≤ 930) : GrahamBound A := by
  exact pair_block 921 930 1831 911 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_194 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 931 ≤ A.card) (hhi : A.card ≤ 938) : GrahamBound A := by
  exact pair_block 931 938 1847 919 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_195 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 939 ≤ A.card) (hhi : A.card ≤ 951) : GrahamBound A := by
  exact pair_block 939 951 1873 937 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_196 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 952 ≤ A.card) (hhi : A.card ≤ 959) : GrahamBound A := by
  exact pair_block 952 959 1889 937 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_197 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 960 ≤ A.card) (hhi : A.card ≤ 971) : GrahamBound A := by
  exact pair_block 960 971 1913 953 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_198 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 972 ≤ A.card) (hhi : A.card ≤ 982) : GrahamBound A := by
  exact pair_block 972 982 1933 967 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_199 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 983 ≤ A.card) (hhi : A.card ≤ 991) : GrahamBound A := by
  exact pair_block 983 991 1951 971 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_200 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 992 ≤ A.card) (hhi : A.card ≤ 1005) : GrahamBound A := by
  exact pair_block 992 1005 1979 991 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_201 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1006 ≤ A.card) (hhi : A.card ≤ 1017) : GrahamBound A := by
  exact pair_block 1006 1017 2003 997 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_202 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1018 ≤ A.card) (hhi : A.card ≤ 1030) : GrahamBound A := by
  exact pair_block 1018 1030 2029 1013 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_203 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1031 ≤ A.card) (hhi : A.card ≤ 1042) : GrahamBound A := by
  exact pair_block 1031 1042 2053 1031 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_204 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1043 ≤ A.card) (hhi : A.card ≤ 1056) : GrahamBound A := by
  exact pair_block 1043 1056 2081 1039 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_205 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1057 ≤ A.card) (hhi : A.card ≤ 1065) : GrahamBound A := by
  exact pair_block 1057 1065 2099 1049 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_206 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1066 ≤ A.card) (hhi : A.card ≤ 1080) : GrahamBound A := by
  exact pair_block 1066 1080 2129 1063 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_207 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1081 ≤ A.card) (hhi : A.card ≤ 1087) : GrahamBound A := by
  exact pair_block 1081 1087 2143 1063 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_208 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1088 ≤ A.card) (hhi : A.card ≤ 1096) : GrahamBound A := by
  exact pair_block 1088 1096 2161 1087 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_209 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1097 ≤ A.card) (hhi : A.card ≤ 1106) : GrahamBound A := by
  exact pair_block 1097 1106 2179 1087 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_210 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1107 ≤ A.card) (hhi : A.card ≤ 1120) : GrahamBound A := by
  exact pair_block 1107 1120 2207 1103 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_211 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1121 ≤ A.card) (hhi : A.card ≤ 1135) : GrahamBound A := by
  exact pair_block 1121 1135 2237 1117 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_212 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1136 ≤ A.card) (hhi : A.card ≤ 1142) : GrahamBound A := by
  exact pair_block 1136 1142 2251 1117 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_213 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1143 ≤ A.card) (hhi : A.card ≤ 1151) : GrahamBound A := by
  exact pair_block 1143 1151 2269 1129 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_214 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1152 ≤ A.card) (hhi : A.card ≤ 1165) : GrahamBound A := by
  exact pair_block 1152 1165 2297 1151 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_215 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1166 ≤ A.card) (hhi : A.card ≤ 1172) : GrahamBound A := by
  exact pair_block 1166 1172 2311 1151 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_216 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1173 ≤ A.card) (hhi : A.card ≤ 1187) : GrahamBound A := by
  exact pair_block 1173 1187 2341 1171 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_217 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1188 ≤ A.card) (hhi : A.card ≤ 1202) : GrahamBound A := by
  exact pair_block 1188 1202 2371 1187 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_218 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1203 ≤ A.card) (hhi : A.card ≤ 1216) : GrahamBound A := by
  exact pair_block 1203 1216 2399 1201 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_219 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1217 ≤ A.card) (hhi : A.card ≤ 1228) : GrahamBound A := by
  exact pair_block 1217 1228 2423 1213 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_220 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1229 ≤ A.card) (hhi : A.card ≤ 1241) : GrahamBound A := by
  exact pair_block 1229 1241 2447 1223 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_221 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1242 ≤ A.card) (hhi : A.card ≤ 1256) : GrahamBound A := by
  exact pair_block 1242 1256 2477 1237 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_222 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1257 ≤ A.card) (hhi : A.card ≤ 1269) : GrahamBound A := by
  exact pair_block 1257 1269 2503 1249 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_223 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1270 ≤ A.card) (hhi : A.card ≤ 1278) : GrahamBound A := by
  exact pair_block 1270 1278 2521 1259 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_224 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1279 ≤ A.card) (hhi : A.card ≤ 1296) : GrahamBound A := by
  exact pair_block 1279 1296 2557 1279 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_225 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1297 ≤ A.card) (hhi : A.card ≤ 1314) : GrahamBound A := by
  exact pair_block 1297 1314 2593 1297 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_226 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1315 ≤ A.card) (hhi : A.card ≤ 1328) : GrahamBound A := by
  exact pair_block 1315 1328 2621 1307 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_227 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1329 ≤ A.card) (hhi : A.card ≤ 1341) : GrahamBound A := by
  exact pair_block 1329 1341 2647 1319 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_228 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1342 ≤ A.card) (hhi : A.card ≤ 1349) : GrahamBound A := by
  exact pair_block 1342 1349 2663 1321 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_229 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1350 ≤ A.card) (hhi : A.card ≤ 1356) : GrahamBound A := by
  exact pair_block 1350 1356 2677 1327 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_230 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1357 ≤ A.card) (hhi : A.card ≤ 1359) : GrahamBound A := by
  exact pair_block 1357 1359 2683 1327 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_231 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1360 ≤ A.card) (hhi : A.card ≤ 1361) : GrahamBound A := by
  exact pair_block 1360 1361 2687 1327 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_232 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1362 ≤ A.card) (hhi : A.card ≤ 1377) : GrahamBound A := by
  exact pair_block 1362 1377 2719 1361 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_233 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1378 ≤ A.card) (hhi : A.card ≤ 1393) : GrahamBound A := by
  exact pair_block 1378 1393 2749 1373 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_234 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1394 ≤ A.card) (hhi : A.card ≤ 1402) : GrahamBound A := by
  exact pair_block 1394 1402 2767 1373 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_235 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1403 ≤ A.card) (hhi : A.card ≤ 1419) : GrahamBound A := by
  exact pair_block 1403 1419 2801 1399 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_236 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1420 ≤ A.card) (hhi : A.card ≤ 1428) : GrahamBound A := by
  exact pair_block 1420 1428 2819 1399 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_237 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1429 ≤ A.card) (hhi : A.card ≤ 1447) : GrahamBound A := by
  exact pair_block 1429 1447 2857 1429 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_238 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1448 ≤ A.card) (hhi : A.card ≤ 1462) : GrahamBound A := by
  exact pair_block 1448 1462 2887 1439 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_239 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1463 ≤ A.card) (hhi : A.card ≤ 1477) : GrahamBound A := by
  exact pair_block 1463 1477 2917 1459 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_240 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1478 ≤ A.card) (hhi : A.card ≤ 1488) : GrahamBound A := by
  exact pair_block 1478 1488 2939 1471 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_241 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1489 ≤ A.card) (hhi : A.card ≤ 1504) : GrahamBound A := by
  exact pair_block 1489 1504 2971 1483 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_242 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1505 ≤ A.card) (hhi : A.card ≤ 1519) : GrahamBound A := by
  exact pair_block 1505 1519 3001 1499 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_243 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1520 ≤ A.card) (hhi : A.card ≤ 1530) : GrahamBound A := by
  exact pair_block 1520 1530 3023 1511 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_244 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1531 ≤ A.card) (hhi : A.card ≤ 1550) : GrahamBound A := by
  exact pair_block 1531 1550 3061 1531 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_245 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1551 ≤ A.card) (hhi : A.card ≤ 1564) : GrahamBound A := by
  exact pair_block 1551 1564 3089 1543 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_246 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1565 ≤ A.card) (hhi : A.card ≤ 1580) : GrahamBound A := by
  exact pair_block 1565 1580 3121 1559 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_247 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1581 ≤ A.card) (hhi : A.card ≤ 1588) : GrahamBound A := by
  exact pair_block 1581 1588 3137 1559 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_248 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1589 ≤ A.card) (hhi : A.card ≤ 1604) : GrahamBound A := by
  exact pair_block 1589 1604 3169 1583 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_249 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1605 ≤ A.card) (hhi : A.card ≤ 1621) : GrahamBound A := by
  exact pair_block 1605 1621 3203 1601 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_250 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1622 ≤ A.card) (hhi : A.card ≤ 1634) : GrahamBound A := by
  exact pair_block 1622 1634 3229 1607 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_251 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1635 ≤ A.card) (hhi : A.card ≤ 1649) : GrahamBound A := by
  exact pair_block 1635 1649 3259 1627 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_252 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1650 ≤ A.card) (hhi : A.card ≤ 1655) : GrahamBound A := by
  exact pair_block 1650 1655 3271 1621 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_253 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1656 ≤ A.card) (hhi : A.card ≤ 1656) : GrahamBound A := by
  have hn : A.card = 1656 := by omega
  apply grahamBound_of_shape_certificate A h0 hg (p:=3271) (j:=1)
  · norm_num
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [hn]; norm_num
  · rw [hn]; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_254 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1657 ≤ A.card) (hhi : A.card ≤ 1676) : GrahamBound A := by
  exact pair_block 1657 1676 3313 1657 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_255 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1677 ≤ A.card) (hhi : A.card ≤ 1691) : GrahamBound A := by
  exact pair_block 1677 1691 3343 1667 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_256 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1692 ≤ A.card) (hhi : A.card ≤ 1701) : GrahamBound A := by
  exact pair_block 1692 1701 3361 1669 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_257 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1702 ≤ A.card) (hhi : A.card ≤ 1716) : GrahamBound A := by
  exact pair_block 1702 1716 3391 1693 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_258 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1717 ≤ A.card) (hhi : A.card ≤ 1727) : GrahamBound A := by
  exact pair_block 1717 1727 3413 1697 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_259 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1728 ≤ A.card) (hhi : A.card ≤ 1745) : GrahamBound A := by
  exact pair_block 1728 1745 3449 1721 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_260 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1746 ≤ A.card) (hhi : A.card ≤ 1755) : GrahamBound A := by
  exact pair_block 1746 1755 3469 1723 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_261 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1756 ≤ A.card) (hhi : A.card ≤ 1770) : GrahamBound A := by
  exact pair_block 1756 1770 3499 1747 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_262 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1771 ≤ A.card) (hhi : A.card ≤ 1785) : GrahamBound A := by
  exact pair_block 1771 1785 3529 1759 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_263 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1786 ≤ A.card) (hhi : A.card ≤ 1800) : GrahamBound A := by
  exact pair_block 1786 1800 3559 1777 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_264 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1801 ≤ A.card) (hhi : A.card ≤ 1817) : GrahamBound A := by
  exact pair_block 1801 1817 3593 1801 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_265 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1818 ≤ A.card) (hhi : A.card ≤ 1832) : GrahamBound A := by
  exact pair_block 1818 1832 3623 1811 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_266 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1833 ≤ A.card) (hhi : A.card ≤ 1850) : GrahamBound A := by
  exact pair_block 1833 1850 3659 1831 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_267 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1851 ≤ A.card) (hhi : A.card ≤ 1870) : GrahamBound A := by
  exact pair_block 1851 1870 3697 1847 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_268 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1871 ≤ A.card) (hhi : A.card ≤ 1891) : GrahamBound A := by
  exact pair_block 1871 1891 3739 1871 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_269 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1892 ≤ A.card) (hhi : A.card ≤ 1911) : GrahamBound A := by
  exact pair_block 1892 1911 3779 1889 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_270 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1912 ≤ A.card) (hhi : A.card ≤ 1923) : GrahamBound A := by
  exact pair_block 1912 1923 3803 1901 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_271 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1924 ≤ A.card) (hhi : A.card ≤ 1938) : GrahamBound A := by
  exact pair_block 1924 1938 3833 1913 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_272 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1939 ≤ A.card) (hhi : A.card ≤ 1953) : GrahamBound A := by
  exact pair_block 1939 1953 3863 1931 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_273 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1954 ≤ A.card) (hhi : A.card ≤ 1966) : GrahamBound A := by
  exact pair_block 1954 1966 3889 1949 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_274 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1967 ≤ A.card) (hhi : A.card ≤ 1980) : GrahamBound A := by
  exact pair_block 1967 1980 3917 1951 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_275 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1981 ≤ A.card) (hhi : A.card ≤ 1995) : GrahamBound A := by
  exact pair_block 1981 1995 3947 1973 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_276 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 1996 ≤ A.card) (hhi : A.card ≤ 2016) : GrahamBound A := by
  exact pair_block 1996 2016 3989 1993 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_277 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2017 ≤ A.card) (hhi : A.card ≤ 2035) : GrahamBound A := by
  exact pair_block 2017 2035 4027 2011 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_278 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2036 ≤ A.card) (hhi : A.card ≤ 2051) : GrahamBound A := by
  exact pair_block 2036 2051 4057 2027 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_279 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2052 ≤ A.card) (hhi : A.card ≤ 2068) : GrahamBound A := by
  exact pair_block 2052 2068 4091 2039 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_280 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2069 ≤ A.card) (hhi : A.card ≤ 2089) : GrahamBound A := by
  exact pair_block 2069 2089 4133 2069 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_281 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2090 ≤ A.card) (hhi : A.card ≤ 2111) : GrahamBound A := by
  exact pair_block 2090 2111 4177 2087 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_282 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2112 ≤ A.card) (hhi : A.card ≤ 2132) : GrahamBound A := by
  exact pair_block 2112 2132 4219 2111 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_283 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2133 ≤ A.card) (hhi : A.card ≤ 2153) : GrahamBound A := by
  exact pair_block 2133 2153 4261 2129 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_284 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2154 ≤ A.card) (hhi : A.card ≤ 2171) : GrahamBound A := by
  exact pair_block 2154 2171 4297 2143 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_285 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2172 ≤ A.card) (hhi : A.card ≤ 2186) : GrahamBound A := by
  exact pair_block 2172 2186 4327 2161 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_286 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2187 ≤ A.card) (hhi : A.card ≤ 2204) : GrahamBound A := by
  exact pair_block 2187 2204 4363 2179 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_287 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2205 ≤ A.card) (hhi : A.card ≤ 2221) : GrahamBound A := by
  exact pair_block 2205 2221 4397 2203 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_288 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2222 ≤ A.card) (hhi : A.card ≤ 2244) : GrahamBound A := by
  exact pair_block 2222 2244 4441 2221 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_289 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2245 ≤ A.card) (hhi : A.card ≤ 2265) : GrahamBound A := by
  exact pair_block 2245 2265 4483 2239 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_290 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2266 ≤ A.card) (hhi : A.card ≤ 2282) : GrahamBound A := by
  exact pair_block 2266 2282 4517 2251 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_291 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2283 ≤ A.card) (hhi : A.card ≤ 2304) : GrahamBound A := by
  exact pair_block 2283 2304 4561 2281 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_292 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2305 ≤ A.card) (hhi : A.card ≤ 2322) : GrahamBound A := by
  exact pair_block 2305 2322 4597 2293 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_293 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2323 ≤ A.card) (hhi : A.card ≤ 2334) : GrahamBound A := by
  exact pair_block 2323 2334 4621 2309 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_294 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2335 ≤ A.card) (hhi : A.card ≤ 2355) : GrahamBound A := by
  exact pair_block 2335 2355 4663 2333 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_295 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2356 ≤ A.card) (hhi : A.card ≤ 2375) : GrahamBound A := by
  exact pair_block 2356 2375 4703 2347 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_296 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2376 ≤ A.card) (hhi : A.card ≤ 2390) : GrahamBound A := by
  exact pair_block 2376 2390 4733 2357 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_297 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2391 ≤ A.card) (hhi : A.card ≤ 2403) : GrahamBound A := by
  exact pair_block 2391 2403 4759 2371 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_298 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2404 ≤ A.card) (hhi : A.card ≤ 2425) : GrahamBound A := by
  exact pair_block 2404 2425 4801 2399 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_299 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2426 ≤ A.card) (hhi : A.card ≤ 2440) : GrahamBound A := by
  exact pair_block 2426 2440 4831 2411 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_300 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2441 ≤ A.card) (hhi : A.card ≤ 2463) : GrahamBound A := by
  exact pair_block 2441 2463 4877 2437 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_301 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2464 ≤ A.card) (hhi : A.card ≤ 2484) : GrahamBound A := by
  exact pair_block 2464 2484 4919 2459 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_302 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2485 ≤ A.card) (hhi : A.card ≤ 2503) : GrahamBound A := by
  exact pair_block 2485 2503 4957 2473 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_303 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2504 ≤ A.card) (hhi : A.card ≤ 2526) : GrahamBound A := by
  exact pair_block 2504 2526 5003 2503 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_304 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2527 ≤ A.card) (hhi : A.card ≤ 2544) : GrahamBound A := by
  exact pair_block 2527 2544 5039 2521 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_305 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2545 ≤ A.card) (hhi : A.card ≤ 2568) : GrahamBound A := by
  exact pair_block 2545 2568 5087 2543 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_306 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2569 ≤ A.card) (hhi : A.card ≤ 2584) : GrahamBound A := by
  exact pair_block 2569 2584 5119 2551 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_307 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2585 ≤ A.card) (hhi : A.card ≤ 2601) : GrahamBound A := by
  exact pair_block 2585 2601 5153 2579 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_308 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2602 ≤ A.card) (hhi : A.card ≤ 2620) : GrahamBound A := by
  exact pair_block 2602 2620 5189 2591 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_309 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2621 ≤ A.card) (hhi : A.card ≤ 2644) : GrahamBound A := by
  exact pair_block 2621 2644 5237 2617 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_310 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2645 ≤ A.card) (hhi : A.card ≤ 2662) : GrahamBound A := by
  exact pair_block 2645 2662 5273 2633 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_311 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2663 ≤ A.card) (hhi : A.card ≤ 2687) : GrahamBound A := by
  exact pair_block 2663 2687 5323 2663 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_312 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2688 ≤ A.card) (hhi : A.card ≤ 2701) : GrahamBound A := by
  exact pair_block 2688 2701 5351 2663 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_313 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2702 ≤ A.card) (hhi : A.card ≤ 2725) : GrahamBound A := by
  exact pair_block 2702 2725 5399 2699 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_314 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2726 ≤ A.card) (hhi : A.card ≤ 2747) : GrahamBound A := by
  exact pair_block 2726 2747 5443 2719 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_315 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2748 ≤ A.card) (hhi : A.card ≤ 2767) : GrahamBound A := by
  exact pair_block 2748 2767 5483 2741 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_316 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2768 ≤ A.card) (hhi : A.card ≤ 2791) : GrahamBound A := by
  exact pair_block 2768 2791 5531 2767 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_317 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2792 ≤ A.card) (hhi : A.card ≤ 2816) : GrahamBound A := by
  exact pair_block 2792 2816 5581 2789 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_318 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2817 ≤ A.card) (hhi : A.card ≤ 2822) : GrahamBound A := by
  exact pair_block 2817 2822 5591 2777 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_319 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2823 ≤ A.card) (hhi : A.card ≤ 2847) : GrahamBound A := by
  exact pair_block 2823 2847 5641 2819 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_320 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2848 ≤ A.card) (hhi : A.card ≤ 2871) : GrahamBound A := by
  exact pair_block 2848 2871 5689 2843 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_321 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2872 ≤ A.card) (hhi : A.card ≤ 2885) : GrahamBound A := by
  exact pair_block 2872 2885 5717 2851 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_322 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2886 ≤ A.card) (hhi : A.card ≤ 2901) : GrahamBound A := by
  exact pair_block 2886 2901 5749 2879 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_323 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2902 ≤ A.card) (hhi : A.card ≤ 2922) : GrahamBound A := by
  exact pair_block 2902 2922 5791 2897 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_324 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2923 ≤ A.card) (hhi : A.card ≤ 2946) : GrahamBound A := by
  exact pair_block 2923 2946 5839 2917 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_325 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2947 ≤ A.card) (hhi : A.card ≤ 2967) : GrahamBound A := by
  exact pair_block 2947 2967 5881 2939 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_326 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2968 ≤ A.card) (hhi : A.card ≤ 2990) : GrahamBound A := by
  exact pair_block 2968 2990 5927 2963 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_327 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 2991 ≤ A.card) (hhi : A.card ≤ 3003) : GrahamBound A := by
  exact pair_block 2991 3003 5953 2963 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_328 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3004 ≤ A.card) (hhi : A.card ≤ 3020) : GrahamBound A := by
  exact pair_block 3004 3020 5987 2999 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_329 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3021 ≤ A.card) (hhi : A.card ≤ 3045) : GrahamBound A := by
  exact pair_block 3021 3045 6037 3019 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_330 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3046 ≤ A.card) (hhi : A.card ≤ 3067) : GrahamBound A := by
  exact pair_block 3046 3067 6079 3037 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_331 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3068 ≤ A.card) (hhi : A.card ≤ 3094) : GrahamBound A := by
  exact pair_block 3068 3094 6133 3067 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_332 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3095 ≤ A.card) (hhi : A.card ≤ 3114) : GrahamBound A := by
  exact pair_block 3095 3114 6173 3079 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_333 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3115 ≤ A.card) (hhi : A.card ≤ 3138) : GrahamBound A := by
  exact pair_block 3115 3138 6221 3109 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_334 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3139 ≤ A.card) (hhi : A.card ≤ 3163) : GrahamBound A := by
  exact pair_block 3139 3163 6271 3137 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_335 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3164 ≤ A.card) (hhi : A.card ≤ 3189) : GrahamBound A := by
  exact pair_block 3164 3189 6323 3163 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_336 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3190 ≤ A.card) (hhi : A.card ≤ 3214) : GrahamBound A := by
  exact pair_block 3190 3214 6373 3187 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_337 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3215 ≤ A.card) (hhi : A.card ≤ 3238) : GrahamBound A := by
  exact pair_block 3215 3238 6421 3209 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_338 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3239 ≤ A.card) (hhi : A.card ≤ 3253) : GrahamBound A := by
  exact pair_block 3239 3253 6451 3217 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_339 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3254 ≤ A.card) (hhi : A.card ≤ 3274) : GrahamBound A := by
  exact pair_block 3254 3274 6491 3251 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_340 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3275 ≤ A.card) (hhi : A.card ≤ 3293) : GrahamBound A := by
  exact pair_block 3275 3293 6529 3257 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_341 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3294 ≤ A.card) (hhi : A.card ≤ 3310) : GrahamBound A := by
  exact pair_block 3294 3310 6563 3271 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_342 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3311 ≤ A.card) (hhi : A.card ≤ 3332) : GrahamBound A := by
  exact pair_block 3311 3332 6607 3299 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_343 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3333 ≤ A.card) (hhi : A.card ≤ 3359) : GrahamBound A := by
  exact pair_block 3333 3359 6661 3329 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_344 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3360 ≤ A.card) (hhi : A.card ≤ 3388) : GrahamBound A := by
  exact pair_block 3360 3388 6719 3359 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_345 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3389 ≤ A.card) (hhi : A.card ≤ 3410) : GrahamBound A := by
  exact pair_block 3389 3410 6763 3389 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_346 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3411 ≤ A.card) (hhi : A.card ≤ 3430) : GrahamBound A := by
  exact pair_block 3411 3430 6803 3407 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_347 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3431 ≤ A.card) (hhi : A.card ≤ 3449) : GrahamBound A := by
  exact pair_block 3431 3449 6841 3413 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_348 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3450 ≤ A.card) (hhi : A.card ≤ 3478) : GrahamBound A := by
  exact pair_block 3450 3478 6899 3449 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_349 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3479 ≤ A.card) (hhi : A.card ≤ 3502) : GrahamBound A := by
  exact pair_block 3479 3502 6947 3469 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_350 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3503 ≤ A.card) (hhi : A.card ≤ 3530) : GrahamBound A := by
  exact pair_block 3503 3530 7001 3499 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_351 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3531 ≤ A.card) (hhi : A.card ≤ 3558) : GrahamBound A := by
  exact pair_block 3531 3558 7057 3527 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_352 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3559 ≤ A.card) (hhi : A.card ≤ 3584) : GrahamBound A := by
  exact pair_block 3559 3584 7109 3557 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_353 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3585 ≤ A.card) (hhi : A.card ≤ 3609) : GrahamBound A := by
  exact pair_block 3585 3609 7159 3581 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_354 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3610 ≤ A.card) (hhi : A.card ≤ 3636) : GrahamBound A := by
  exact pair_block 3610 3636 7213 3607 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_355 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3637 ≤ A.card) (hhi : A.card ≤ 3656) : GrahamBound A := by
  exact pair_block 3637 3656 7253 3617 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_356 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3657 ≤ A.card) (hhi : A.card ≤ 3678) : GrahamBound A := by
  exact pair_block 3657 3678 7297 3643 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_357 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3679 ≤ A.card) (hhi : A.card ≤ 3705) : GrahamBound A := by
  exact pair_block 3679 3705 7351 3673 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_358 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3706 ≤ A.card) (hhi : A.card ≤ 3726) : GrahamBound A := by
  exact pair_block 3706 3726 7393 3691 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_359 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3727 ≤ A.card) (hhi : A.card ≤ 3756) : GrahamBound A := by
  exact pair_block 3727 3756 7451 3727 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_360 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3757 ≤ A.card) (hhi : A.card ≤ 3775) : GrahamBound A := by
  exact pair_block 3757 3775 7489 3733 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_361 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3776 ≤ A.card) (hhi : A.card ≤ 3801) : GrahamBound A := by
  exact pair_block 3776 3801 7541 3767 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_362 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3802 ≤ A.card) (hhi : A.card ≤ 3826) : GrahamBound A := by
  exact pair_block 3802 3826 7591 3793 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_363 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3827 ≤ A.card) (hhi : A.card ≤ 3855) : GrahamBound A := by
  exact pair_block 3827 3855 7649 3823 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_364 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3856 ≤ A.card) (hhi : A.card ≤ 3882) : GrahamBound A := by
  exact pair_block 3856 3882 7703 3847 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_365 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3883 ≤ A.card) (hhi : A.card ≤ 3910) : GrahamBound A := by
  exact pair_block 3883 3910 7759 3877 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_366 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3911 ≤ A.card) (hhi : A.card ≤ 3939) : GrahamBound A := by
  exact pair_block 3911 3939 7817 3907 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_367 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3940 ≤ A.card) (hhi : A.card ≤ 3964) : GrahamBound A := by
  exact pair_block 3940 3964 7867 3929 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_368 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3965 ≤ A.card) (hhi : A.card ≤ 3984) : GrahamBound A := by
  exact pair_block 3965 3984 7907 3943 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_369 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 3985 ≤ A.card) (hhi : A.card ≤ 4007) : GrahamBound A := by
  exact pair_block 3985 4007 7951 3967 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_370 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4008 ≤ A.card) (hhi : A.card ≤ 4037) : GrahamBound A := by
  exact pair_block 4008 4037 8011 4003 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_371 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4038 ≤ A.card) (hhi : A.card ≤ 4061) : GrahamBound A := by
  exact pair_block 4038 4061 8059 4021 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_372 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4062 ≤ A.card) (hhi : A.card ≤ 4090) : GrahamBound A := by
  exact pair_block 4062 4090 8117 4057 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_373 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4091 ≤ A.card) (hhi : A.card ≤ 4121) : GrahamBound A := by
  exact pair_block 4091 4121 8179 4091 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_374 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4122 ≤ A.card) (hhi : A.card ≤ 4148) : GrahamBound A := by
  exact pair_block 4122 4148 8233 4111 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_375 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4149 ≤ A.card) (hhi : A.card ≤ 4175) : GrahamBound A := by
  exact pair_block 4149 4175 8287 4139 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_376 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4176 ≤ A.card) (hhi : A.card ≤ 4196) : GrahamBound A := by
  exact pair_block 4176 4196 8329 4153 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_377 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4197 ≤ A.card) (hhi : A.card ≤ 4216) : GrahamBound A := by
  exact pair_block 4197 4216 8369 4177 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_378 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4217 ≤ A.card) (hhi : A.card ≤ 4247) : GrahamBound A := by
  exact pair_block 4217 4247 8431 4217 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_379 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4248 ≤ A.card) (hhi : A.card ≤ 4266) : GrahamBound A := by
  exact pair_block 4248 4266 8467 4219 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_380 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4267 ≤ A.card) (hhi : A.card ≤ 4296) : GrahamBound A := by
  exact pair_block 4267 4296 8527 4261 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_381 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4297 ≤ A.card) (hhi : A.card ≤ 4323) : GrahamBound A := by
  exact pair_block 4297 4323 8581 4289 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_382 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4324 ≤ A.card) (hhi : A.card ≤ 4337) : GrahamBound A := by
  exact pair_block 4324 4337 8609 4289 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_383 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4338 ≤ A.card) (hhi : A.card ≤ 4367) : GrahamBound A := by
  exact pair_block 4338 4367 8669 4337 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_384 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4368 ≤ A.card) (hhi : A.card ≤ 4398) : GrahamBound A := by
  exact pair_block 4368 4398 8731 4363 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_385 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4399 ≤ A.card) (hhi : A.card ≤ 4424) : GrahamBound A := by
  exact pair_block 4399 4424 8783 4391 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_386 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4425 ≤ A.card) (hhi : A.card ≤ 4452) : GrahamBound A := by
  exact pair_block 4425 4452 8839 4421 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_387 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4453 ≤ A.card) (hhi : A.card ≤ 4479) : GrahamBound A := by
  exact pair_block 4453 4479 8893 4441 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_388 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4480 ≤ A.card) (hhi : A.card ≤ 4503) : GrahamBound A := by
  exact pair_block 4480 4503 8941 4463 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_389 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4504 ≤ A.card) (hhi : A.card ≤ 4519) : GrahamBound A := by
  exact pair_block 4504 4519 8971 4481 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_390 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4520 ≤ A.card) (hhi : A.card ≤ 4548) : GrahamBound A := by
  exact pair_block 4520 4548 9029 4513 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_391 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4549 ≤ A.card) (hhi : A.card ≤ 4579) : GrahamBound A := by
  exact pair_block 4549 4579 9091 4547 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_392 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4580 ≤ A.card) (hhi : A.card ≤ 4602) : GrahamBound A := by
  exact pair_block 4580 4602 9137 4561 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_393 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4603 ≤ A.card) (hhi : A.card ≤ 4635) : GrahamBound A := by
  exact pair_block 4603 4635 9203 4603 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_394 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4636 ≤ A.card) (hhi : A.card ≤ 4662) : GrahamBound A := by
  exact pair_block 4636 4662 9257 4621 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_395 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4663 ≤ A.card) (hhi : A.card ≤ 4695) : GrahamBound A := by
  exact pair_block 4663 4695 9323 4663 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_396 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4696 ≤ A.card) (hhi : A.card ≤ 4722) : GrahamBound A := by
  exact pair_block 4696 4722 9377 4691 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_397 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4723 ≤ A.card) (hhi : A.card ≤ 4753) : GrahamBound A := by
  exact pair_block 4723 4753 9439 4721 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_398 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4754 ≤ A.card) (hhi : A.card ≤ 4782) : GrahamBound A := by
  exact pair_block 4754 4782 9497 4751 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_399 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4783 ≤ A.card) (hhi : A.card ≤ 4810) : GrahamBound A := by
  exact pair_block 4783 4810 9551 4783 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_400 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4811 ≤ A.card) (hhi : A.card ≤ 4835) : GrahamBound A := by
  exact pair_block 4811 4835 9601 4793 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_401 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4836 ≤ A.card) (hhi : A.card ≤ 4865) : GrahamBound A := by
  exact pair_block 4836 4865 9661 4831 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_402 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4866 ≤ A.card) (hhi : A.card ≤ 4895) : GrahamBound A := by
  exact pair_block 4866 4895 9721 4861 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_403 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4896 ≤ A.card) (hhi : A.card ≤ 4925) : GrahamBound A := by
  exact pair_block 4896 4925 9781 4889 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_404 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4926 ≤ A.card) (hhi : A.card ≤ 4954) : GrahamBound A := by
  exact pair_block 4926 4954 9839 4919 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_405 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4955 ≤ A.card) (hhi : A.card ≤ 4985) : GrahamBound A := by
  exact pair_block 4955 4985 9901 4951 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_406 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 4986 ≤ A.card) (hhi : A.card ≤ 5009) : GrahamBound A := by
  exact pair_block 4986 5009 9949 4967 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_407 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5010 ≤ A.card) (hhi : A.card ≤ 5039) : GrahamBound A := by
  exact pair_block 5010 5039 10009 4999 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_408 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5040 ≤ A.card) (hhi : A.card ≤ 5074) : GrahamBound A := by
  exact pair_block 5040 5074 10079 5039 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_409 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5075 ≤ A.card) (hhi : A.card ≤ 5102) : GrahamBound A := by
  exact pair_block 5075 5102 10133 5059 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_410 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5103 ≤ A.card) (hhi : A.card ≤ 5132) : GrahamBound A := by
  exact pair_block 5103 5132 10193 5099 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_411 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5133 ≤ A.card) (hhi : A.card ≤ 5159) : GrahamBound A := by
  exact pair_block 5133 5159 10247 5119 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_412 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5160 ≤ A.card) (hhi : A.card ≤ 5192) : GrahamBound A := by
  exact pair_block 5160 5192 10313 5153 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_413 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5193 ≤ A.card) (hhi : A.card ≤ 5220) : GrahamBound A := by
  exact pair_block 5193 5220 10369 5179 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_414 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5221 ≤ A.card) (hhi : A.card ≤ 5250) : GrahamBound A := by
  exact pair_block 5221 5250 10429 5209 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_415 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5251 ≤ A.card) (hhi : A.card ≤ 5279) : GrahamBound A := by
  exact pair_block 5251 5279 10487 5237 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_416 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5280 ≤ A.card) (hhi : A.card ≤ 5315) : GrahamBound A := by
  exact pair_block 5280 5315 10559 5279 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_417 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5316 ≤ A.card) (hhi : A.card ≤ 5342) : GrahamBound A := by
  exact pair_block 5316 5342 10613 5297 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_418 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5343 ≤ A.card) (hhi : A.card ≤ 5370) : GrahamBound A := by
  exact pair_block 5343 5370 10667 5333 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_419 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5371 ≤ A.card) (hhi : A.card ≤ 5392) : GrahamBound A := by
  exact pair_block 5371 5392 10711 5347 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_420 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5393 ≤ A.card) (hhi : A.card ≤ 5427) : GrahamBound A := by
  exact pair_block 5393 5427 10781 5393 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_421 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5428 ≤ A.card) (hhi : A.card ≤ 5460) : GrahamBound A := by
  exact pair_block 5428 5460 10847 5419 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_422 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5461 ≤ A.card) (hhi : A.card ≤ 5491) : GrahamBound A := by
  exact pair_block 5461 5491 10909 5449 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_423 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5492 ≤ A.card) (hhi : A.card ≤ 5523) : GrahamBound A := by
  exact pair_block 5492 5523 10973 5483 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_424 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5524 ≤ A.card) (hhi : A.card ≤ 5550) : GrahamBound A := by
  exact pair_block 5524 5550 11027 5503 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_425 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5551 ≤ A.card) (hhi : A.card ≤ 5572) : GrahamBound A := by
  exact pair_block 5551 5572 11071 5521 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_426 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5573 ≤ A.card) (hhi : A.card ≤ 5602) : GrahamBound A := by
  exact pair_block 5573 5602 11131 5563 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_427 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5603 ≤ A.card) (hhi : A.card ≤ 5625) : GrahamBound A := by
  exact pair_block 5603 5625 11177 5581 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_428 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5626 ≤ A.card) (hhi : A.card ≤ 5659) : GrahamBound A := by
  exact pair_block 5626 5659 11243 5623 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_429 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5660 ≤ A.card) (hhi : A.card ≤ 5696) : GrahamBound A := by
  exact pair_block 5660 5696 11317 5657 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_430 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5697 ≤ A.card) (hhi : A.card ≤ 5729) : GrahamBound A := by
  exact pair_block 5697 5729 11383 5689 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_431 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5730 ≤ A.card) (hhi : A.card ≤ 5761) : GrahamBound A := by
  exact pair_block 5730 5761 11447 5717 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_432 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5762 ≤ A.card) (hhi : A.card ≤ 5789) : GrahamBound A := by
  exact pair_block 5762 5789 11503 5741 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_433 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5790 ≤ A.card) (hhi : A.card ≤ 5813) : GrahamBound A := by
  exact pair_block 5790 5813 11551 5779 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_434 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5814 ≤ A.card) (hhi : A.card ≤ 5848) : GrahamBound A := by
  exact pair_block 5814 5848 11621 5807 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_435 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5849 ≤ A.card) (hhi : A.card ≤ 5882) : GrahamBound A := by
  exact pair_block 5849 5882 11689 5843 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_436 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5883 ≤ A.card) (hhi : A.card ≤ 5909) : GrahamBound A := by
  exact pair_block 5883 5909 11743 5861 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_437 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5910 ≤ A.card) (hhi : A.card ≤ 5944) : GrahamBound A := by
  exact pair_block 5910 5944 11813 5903 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_438 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5945 ≤ A.card) (hhi : A.card ≤ 5972) : GrahamBound A := by
  exact pair_block 5945 5972 11867 5923 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_439 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 5973 ≤ A.card) (hhi : A.card ≤ 6000) : GrahamBound A := by
  exact pair_block 5973 6000 11923 5953 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_440 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6001 ≤ A.card) (hhi : A.card ≤ 6032) : GrahamBound A := by
  exact pair_block 6001 6032 11987 5987 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_441 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6033 ≤ A.card) (hhi : A.card ≤ 6063) : GrahamBound A := by
  exact pair_block 6033 6063 12049 6029 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_442 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6064 ≤ A.card) (hhi : A.card ≤ 6095) : GrahamBound A := by
  exact pair_block 6064 6095 12113 6053 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_443 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6096 ≤ A.card) (hhi : A.card ≤ 6120) : GrahamBound A := by
  exact pair_block 6096 6120 12163 6067 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_444 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6121 ≤ A.card) (hhi : A.card ≤ 6159) : GrahamBound A := by
  exact pair_block 6121 6159 12241 6121 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_445 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6160 ≤ A.card) (hhi : A.card ≤ 6189) : GrahamBound A := by
  exact pair_block 6160 6189 12301 6143 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_446 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6190 ≤ A.card) (hhi : A.card ≤ 6212) : GrahamBound A := by
  exact pair_block 6190 6212 12347 6163 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_447 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6213 ≤ A.card) (hhi : A.card ≤ 6249) : GrahamBound A := by
  exact pair_block 6213 6249 12421 6211 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_448 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6250 ≤ A.card) (hhi : A.card ≤ 6288) : GrahamBound A := by
  exact pair_block 6250 6288 12497 6247 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_449 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6289 ≤ A.card) (hhi : A.card ≤ 6324) : GrahamBound A := by
  exact pair_block 6289 6324 12569 6287 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_450 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6325 ≤ A.card) (hhi : A.card ≤ 6363) : GrahamBound A := by
  exact pair_block 6325 6363 12647 6323 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_451 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6364 ≤ A.card) (hhi : A.card ≤ 6400) : GrahamBound A := by
  exact pair_block 6364 6400 12721 6359 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_452 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6401 ≤ A.card) (hhi : A.card ≤ 6435) : GrahamBound A := by
  exact pair_block 6401 6435 12791 6397 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_453 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6436 ≤ A.card) (hhi : A.card ≤ 6466) : GrahamBound A := by
  exact pair_block 6436 6466 12853 6421 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_454 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6467 ≤ A.card) (hhi : A.card ≤ 6498) : GrahamBound A := by
  exact pair_block 6467 6498 12917 6451 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_455 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6499 ≤ A.card) (hhi : A.card ≤ 6531) : GrahamBound A := by
  exact pair_block 6499 6531 12983 6491 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_456 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6532 ≤ A.card) (hhi : A.card ≤ 6564) : GrahamBound A := by
  exact pair_block 6532 6564 13049 6521 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_457 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6565 ≤ A.card) (hhi : A.card ≤ 6604) : GrahamBound A := by
  exact pair_block 6565 6604 13127 6563 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_458 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6605 ≤ A.card) (hhi : A.card ≤ 6634) : GrahamBound A := by
  exact pair_block 6605 6634 13187 6599 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_459 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6635 ≤ A.card) (hhi : A.card ≤ 6665) : GrahamBound A := by
  exact pair_block 6635 6665 13249 6619 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_460 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6666 ≤ A.card) (hhi : A.card ≤ 6704) : GrahamBound A := by
  exact pair_block 6666 6704 13327 6661 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_461 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6705 ≤ A.card) (hhi : A.card ≤ 6740) : GrahamBound A := by
  exact pair_block 6705 6740 13399 6701 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_462 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6741 ≤ A.card) (hhi : A.card ≤ 6779) : GrahamBound A := by
  exact pair_block 6741 6779 13477 6737 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_463 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6780 ≤ A.card) (hhi : A.card ≤ 6817) : GrahamBound A := by
  exact pair_block 6780 6817 13553 6779 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_464 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6818 ≤ A.card) (hhi : A.card ≤ 6850) : GrahamBound A := by
  exact pair_block 6818 6850 13619 6803 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_465 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6851 ≤ A.card) (hhi : A.card ≤ 6886) : GrahamBound A := by
  exact pair_block 6851 6886 13691 6841 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_466 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6887 ≤ A.card) (hhi : A.card ≤ 6922) : GrahamBound A := by
  exact pair_block 6887 6922 13763 6883 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_467 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6923 ≤ A.card) (hhi : A.card ≤ 6957) : GrahamBound A := by
  exact pair_block 6923 6957 13831 6911 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_468 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6958 ≤ A.card) (hhi : A.card ≤ 6995) : GrahamBound A := by
  exact pair_block 6958 6995 13907 6949 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma block_469 (A : Finset ℕ) (h0 : 0 ∉ A) (hg : A.gcd id=1)
    (hlo : 6996 ≤ A.card) (hhi : A.card ≤ 7000) : GrahamBound A := by
  exact pair_block 6996 7000 13967 6971 (by omega) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) (by omega)
    A h0 hg hlo hhi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma finite_normalized_core (A : Finset ℕ) (h0 : 0 ∉ A)
    (hg : A.gcd id=1) (hl : 11 ≤ A.card) (hu : A.card ≤ 7000) : GrahamBound A := by
  by_cases h235 : A.card ≤ 1402
  · by_cases h117 : A.card ≤ 339
    · by_cases h58 : A.card ≤ 112
      · by_cases h29 : A.card ≤ 49
        · by_cases h14 : A.card ≤ 27
          · by_cases h7 : A.card ≤ 18
            · by_cases h3 : A.card ≤ 14
              · by_cases h1 : A.card ≤ 11
                · exact block_0 A h0 hg (by omega) (by omega)
                · by_cases h2 : A.card ≤ 13
                  · exact block_1 A h0 hg (by omega) (by omega)
                  · exact block_2 A h0 hg (by omega) (by omega)
              · by_cases h5 : A.card ≤ 16
                · by_cases h4 : A.card ≤ 15
                  · exact block_3 A h0 hg (by omega) (by omega)
                  · exact block_4 A h0 hg (by omega) (by omega)
                · by_cases h6 : A.card ≤ 17
                  · exact block_5 A h0 hg (by omega) (by omega)
                  · exact block_6 A h0 hg (by omega) (by omega)
            · by_cases h10 : A.card ≤ 22
              · by_cases h8 : A.card ≤ 20
                · exact block_7 A h0 hg (by omega) (by omega)
                · by_cases h9 : A.card ≤ 21
                  · exact block_8 A h0 hg (by omega) (by omega)
                  · exact block_9 A h0 hg (by omega) (by omega)
              · by_cases h12 : A.card ≤ 25
                · by_cases h11 : A.card ≤ 23
                  · exact block_10 A h0 hg (by omega) (by omega)
                  · exact block_11 A h0 hg (by omega) (by omega)
                · by_cases h13 : A.card ≤ 26
                  · exact block_12 A h0 hg (by omega) (by omega)
                  · exact block_13 A h0 hg (by omega) (by omega)
          · by_cases h21 : A.card ≤ 36
            · by_cases h17 : A.card ≤ 32
              · by_cases h15 : A.card ≤ 28
                · exact block_14 A h0 hg (by omega) (by omega)
                · by_cases h16 : A.card ≤ 29
                  · exact block_15 A h0 hg (by omega) (by omega)
                  · exact block_16 A h0 hg (by omega) (by omega)
              · by_cases h19 : A.card ≤ 34
                · by_cases h18 : A.card ≤ 33
                  · exact block_17 A h0 hg (by omega) (by omega)
                  · exact block_18 A h0 hg (by omega) (by omega)
                · by_cases h20 : A.card ≤ 35
                  · exact block_19 A h0 hg (by omega) (by omega)
                  · exact block_20 A h0 hg (by omega) (by omega)
            · by_cases h25 : A.card ≤ 44
              · by_cases h23 : A.card ≤ 40
                · by_cases h22 : A.card ≤ 39
                  · exact block_21 A h0 hg (by omega) (by omega)
                  · exact block_22 A h0 hg (by omega) (by omega)
                · by_cases h24 : A.card ≤ 42
                  · exact block_23 A h0 hg (by omega) (by omega)
                  · exact block_24 A h0 hg (by omega) (by omega)
              · by_cases h27 : A.card ≤ 47
                · by_cases h26 : A.card ≤ 45
                  · exact block_25 A h0 hg (by omega) (by omega)
                  · exact block_26 A h0 hg (by omega) (by omega)
                · by_cases h28 : A.card ≤ 48
                  · exact block_27 A h0 hg (by omega) (by omega)
                  · exact block_28 A h0 hg (by omega) (by omega)
        · by_cases h43 : A.card ≤ 74
          · by_cases h36 : A.card ≤ 63
            · by_cases h32 : A.card ≤ 58
              · by_cases h30 : A.card ≤ 52
                · exact block_29 A h0 hg (by omega) (by omega)
                · by_cases h31 : A.card ≤ 55
                  · exact block_30 A h0 hg (by omega) (by omega)
                  · exact block_31 A h0 hg (by omega) (by omega)
              · by_cases h34 : A.card ≤ 61
                · by_cases h33 : A.card ≤ 60
                  · exact block_32 A h0 hg (by omega) (by omega)
                  · exact block_33 A h0 hg (by omega) (by omega)
                · by_cases h35 : A.card ≤ 62
                  · exact block_34 A h0 hg (by omega) (by omega)
                  · exact block_35 A h0 hg (by omega) (by omega)
            · by_cases h39 : A.card ≤ 67
              · by_cases h37 : A.card ≤ 64
                · exact block_36 A h0 hg (by omega) (by omega)
                · by_cases h38 : A.card ≤ 65
                  · exact block_37 A h0 hg (by omega) (by omega)
                  · exact block_38 A h0 hg (by omega) (by omega)
              · by_cases h41 : A.card ≤ 72
                · by_cases h40 : A.card ≤ 69
                  · exact block_39 A h0 hg (by omega) (by omega)
                  · exact block_40 A h0 hg (by omega) (by omega)
                · by_cases h42 : A.card ≤ 73
                  · exact block_41 A h0 hg (by omega) (by omega)
                  · exact block_42 A h0 hg (by omega) (by omega)
          · by_cases h50 : A.card ≤ 95
            · by_cases h46 : A.card ≤ 82
              · by_cases h44 : A.card ≤ 75
                · exact block_43 A h0 hg (by omega) (by omega)
                · by_cases h45 : A.card ≤ 78
                  · exact block_44 A h0 hg (by omega) (by omega)
                  · exact block_45 A h0 hg (by omega) (by omega)
              · by_cases h48 : A.card ≤ 88
                · by_cases h47 : A.card ≤ 86
                  · exact block_46 A h0 hg (by omega) (by omega)
                  · exact block_47 A h0 hg (by omega) (by omega)
                · by_cases h49 : A.card ≤ 91
                  · exact block_48 A h0 hg (by omega) (by omega)
                  · exact block_49 A h0 hg (by omega) (by omega)
            · by_cases h54 : A.card ≤ 105
              · by_cases h52 : A.card ≤ 101
                · by_cases h51 : A.card ≤ 96
                  · exact block_50 A h0 hg (by omega) (by omega)
                  · exact block_51 A h0 hg (by omega) (by omega)
                · by_cases h53 : A.card ≤ 104
                  · exact block_52 A h0 hg (by omega) (by omega)
                  · exact block_53 A h0 hg (by omega) (by omega)
              · by_cases h56 : A.card ≤ 110
                · by_cases h55 : A.card ≤ 106
                  · exact block_54 A h0 hg (by omega) (by omega)
                  · exact block_55 A h0 hg (by omega) (by omega)
                · by_cases h57 : A.card ≤ 111
                  · exact block_56 A h0 hg (by omega) (by omega)
                  · exact block_57 A h0 hg (by omega) (by omega)
      · by_cases h87 : A.card ≤ 201
        · by_cases h72 : A.card ≤ 148
          · by_cases h65 : A.card ≤ 125
            · by_cases h61 : A.card ≤ 121
              · by_cases h59 : A.card ≤ 116
                · exact block_58 A h0 hg (by omega) (by omega)
                · by_cases h60 : A.card ≤ 119
                  · exact block_59 A h0 hg (by omega) (by omega)
                  · exact block_60 A h0 hg (by omega) (by omega)
              · by_cases h63 : A.card ≤ 123
                · by_cases h62 : A.card ≤ 122
                  · exact block_61 A h0 hg (by omega) (by omega)
                  · exact block_62 A h0 hg (by omega) (by omega)
                · by_cases h64 : A.card ≤ 124
                  · exact block_63 A h0 hg (by omega) (by omega)
                  · exact block_64 A h0 hg (by omega) (by omega)
            · by_cases h68 : A.card ≤ 137
              · by_cases h66 : A.card ≤ 126
                · exact block_65 A h0 hg (by omega) (by omega)
                · by_cases h67 : A.card ≤ 131
                  · exact block_66 A h0 hg (by omega) (by omega)
                  · exact block_67 A h0 hg (by omega) (by omega)
              · by_cases h70 : A.card ≤ 146
                · by_cases h69 : A.card ≤ 141
                  · exact block_68 A h0 hg (by omega) (by omega)
                  · exact block_69 A h0 hg (by omega) (by omega)
                · by_cases h71 : A.card ≤ 147
                  · exact block_70 A h0 hg (by omega) (by omega)
                  · exact block_71 A h0 hg (by omega) (by omega)
          · by_cases h79 : A.card ≤ 165
            · by_cases h75 : A.card ≤ 154
              · by_cases h73 : A.card ≤ 152
                · exact block_72 A h0 hg (by omega) (by omega)
                · by_cases h74 : A.card ≤ 153
                  · exact block_73 A h0 hg (by omega) (by omega)
                  · exact block_74 A h0 hg (by omega) (by omega)
              · by_cases h77 : A.card ≤ 159
                · by_cases h76 : A.card ≤ 155
                  · exact block_75 A h0 hg (by omega) (by omega)
                  · exact block_76 A h0 hg (by omega) (by omega)
                · by_cases h78 : A.card ≤ 164
                  · exact block_77 A h0 hg (by omega) (by omega)
                  · exact block_78 A h0 hg (by omega) (by omega)
            · by_cases h83 : A.card ≤ 181
              · by_cases h81 : A.card ≤ 171
                · by_cases h80 : A.card ≤ 166
                  · exact block_79 A h0 hg (by omega) (by omega)
                  · exact block_80 A h0 hg (by omega) (by omega)
                · by_cases h82 : A.card ≤ 175
                  · exact block_81 A h0 hg (by omega) (by omega)
                  · exact block_82 A h0 hg (by omega) (by omega)
              · by_cases h85 : A.card ≤ 190
                · by_cases h84 : A.card ≤ 186
                  · exact block_83 A h0 hg (by omega) (by omega)
                  · exact block_84 A h0 hg (by omega) (by omega)
                · by_cases h86 : A.card ≤ 196
                  · exact block_85 A h0 hg (by omega) (by omega)
                  · exact block_86 A h0 hg (by omega) (by omega)
        · by_cases h102 : A.card ≤ 262
          · by_cases h94 : A.card ≤ 219
            · by_cases h90 : A.card ≤ 209
              · by_cases h88 : A.card ≤ 207
                · exact block_87 A h0 hg (by omega) (by omega)
                · by_cases h89 : A.card ≤ 208
                  · exact block_88 A h0 hg (by omega) (by omega)
                  · exact block_89 A h0 hg (by omega) (by omega)
              · by_cases h92 : A.card ≤ 217
                · by_cases h91 : A.card ≤ 211
                  · exact block_90 A h0 hg (by omega) (by omega)
                  · exact block_91 A h0 hg (by omega) (by omega)
                · by_cases h93 : A.card ≤ 218
                  · exact block_92 A h0 hg (by omega) (by omega)
                  · exact block_93 A h0 hg (by omega) (by omega)
            · by_cases h98 : A.card ≤ 241
              · by_cases h96 : A.card ≤ 228
                · by_cases h95 : A.card ≤ 222
                  · exact block_94 A h0 hg (by omega) (by omega)
                  · exact block_95 A h0 hg (by omega) (by omega)
                · by_cases h97 : A.card ≤ 236
                  · exact block_96 A h0 hg (by omega) (by omega)
                  · exact block_97 A h0 hg (by omega) (by omega)
              · by_cases h100 : A.card ≤ 251
                · by_cases h99 : A.card ≤ 247
                  · exact block_98 A h0 hg (by omega) (by omega)
                  · exact block_99 A h0 hg (by omega) (by omega)
                · by_cases h101 : A.card ≤ 259
                  · exact block_100 A h0 hg (by omega) (by omega)
                  · exact block_101 A h0 hg (by omega) (by omega)
          · by_cases h109 : A.card ≤ 302
            · by_cases h105 : A.card ≤ 278
              · by_cases h103 : A.card ≤ 269
                · exact block_102 A h0 hg (by omega) (by omega)
                · by_cases h104 : A.card ≤ 270
                  · exact block_103 A h0 hg (by omega) (by omega)
                  · exact block_104 A h0 hg (by omega) (by omega)
              · by_cases h107 : A.card ≤ 289
                · by_cases h106 : A.card ≤ 281
                  · exact block_105 A h0 hg (by omega) (by omega)
                  · exact block_106 A h0 hg (by omega) (by omega)
                · by_cases h108 : A.card ≤ 294
                  · exact block_107 A h0 hg (by omega) (by omega)
                  · exact block_108 A h0 hg (by omega) (by omega)
            · by_cases h113 : A.card ≤ 318
              · by_cases h111 : A.card ≤ 308
                · by_cases h110 : A.card ≤ 305
                  · exact block_109 A h0 hg (by omega) (by omega)
                  · exact block_110 A h0 hg (by omega) (by omega)
                · by_cases h112 : A.card ≤ 315
                  · exact block_111 A h0 hg (by omega) (by omega)
                  · exact block_112 A h0 hg (by omega) (by omega)
              · by_cases h115 : A.card ≤ 329
                · by_cases h114 : A.card ≤ 324
                  · exact block_113 A h0 hg (by omega) (by omega)
                  · exact block_114 A h0 hg (by omega) (by omega)
                · by_cases h116 : A.card ≤ 332
                  · exact block_115 A h0 hg (by omega) (by omega)
                  · exact block_116 A h0 hg (by omega) (by omega)
    · by_cases h176 : A.card ≤ 769
      · by_cases h146 : A.card ≤ 537
        · by_cases h131 : A.card ≤ 430
          · by_cases h124 : A.card ≤ 390
            · by_cases h120 : A.card ≤ 359
              · by_cases h118 : A.card ≤ 347
                · exact block_117 A h0 hg (by omega) (by omega)
                · by_cases h119 : A.card ≤ 354
                  · exact block_118 A h0 hg (by omega) (by omega)
                  · exact block_119 A h0 hg (by omega) (by omega)
              · by_cases h122 : A.card ≤ 376
                · by_cases h121 : A.card ≤ 368
                  · exact block_120 A h0 hg (by omega) (by omega)
                  · exact block_121 A h0 hg (by omega) (by omega)
                · by_cases h123 : A.card ≤ 381
                  · exact block_122 A h0 hg (by omega) (by omega)
                  · exact block_123 A h0 hg (by omega) (by omega)
            · by_cases h127 : A.card ≤ 408
              · by_cases h125 : A.card ≤ 396
                · exact block_124 A h0 hg (by omega) (by omega)
                · by_cases h126 : A.card ≤ 403
                  · exact block_125 A h0 hg (by omega) (by omega)
                  · exact block_126 A h0 hg (by omega) (by omega)
              · by_cases h129 : A.card ≤ 421
                · by_cases h128 : A.card ≤ 415
                  · exact block_127 A h0 hg (by omega) (by omega)
                  · exact block_128 A h0 hg (by omega) (by omega)
                · by_cases h130 : A.card ≤ 429
                  · exact block_129 A h0 hg (by omega) (by omega)
                  · exact block_130 A h0 hg (by omega) (by omega)
          · by_cases h138 : A.card ≤ 475
            · by_cases h134 : A.card ≤ 454
              · by_cases h132 : A.card ≤ 439
                · exact block_131 A h0 hg (by omega) (by omega)
                · by_cases h133 : A.card ≤ 448
                  · exact block_132 A h0 hg (by omega) (by omega)
                  · exact block_133 A h0 hg (by omega) (by omega)
              · by_cases h136 : A.card ≤ 456
                · by_cases h135 : A.card ≤ 455
                  · exact block_134 A h0 hg (by omega) (by omega)
                  · exact block_135 A h0 hg (by omega) (by omega)
                · by_cases h137 : A.card ≤ 466
                  · exact block_136 A h0 hg (by omega) (by omega)
                  · exact block_137 A h0 hg (by omega) (by omega)
            · by_cases h142 : A.card ≤ 502
              · by_cases h140 : A.card ≤ 487
                · by_cases h139 : A.card ≤ 481
                  · exact block_138 A h0 hg (by omega) (by omega)
                  · exact block_139 A h0 hg (by omega) (by omega)
                · by_cases h141 : A.card ≤ 496
                  · exact block_140 A h0 hg (by omega) (by omega)
                  · exact block_141 A h0 hg (by omega) (by omega)
              · by_cases h144 : A.card ≤ 520
                · by_cases h143 : A.card ≤ 509
                  · exact block_142 A h0 hg (by omega) (by omega)
                  · exact block_143 A h0 hg (by omega) (by omega)
                · by_cases h145 : A.card ≤ 530
                  · exact block_144 A h0 hg (by omega) (by omega)
                  · exact block_145 A h0 hg (by omega) (by omega)
        · by_cases h161 : A.card ≤ 676
          · by_cases h153 : A.card ≤ 597
            · by_cases h149 : A.card ≤ 558
              · by_cases h147 : A.card ≤ 542
                · exact block_146 A h0 hg (by omega) (by omega)
                · by_cases h148 : A.card ≤ 546
                  · exact block_147 A h0 hg (by omega) (by omega)
                  · exact block_148 A h0 hg (by omega) (by omega)
              · by_cases h151 : A.card ≤ 576
                · by_cases h150 : A.card ≤ 566
                  · exact block_149 A h0 hg (by omega) (by omega)
                  · exact block_150 A h0 hg (by omega) (by omega)
                · by_cases h152 : A.card ≤ 588
                  · exact block_151 A h0 hg (by omega) (by omega)
                  · exact block_152 A h0 hg (by omega) (by omega)
            · by_cases h157 : A.card ≤ 630
              · by_cases h155 : A.card ≤ 612
                · by_cases h154 : A.card ≤ 605
                  · exact block_153 A h0 hg (by omega) (by omega)
                  · exact block_154 A h0 hg (by omega) (by omega)
                · by_cases h156 : A.card ≤ 623
                  · exact block_155 A h0 hg (by omega) (by omega)
                  · exact block_156 A h0 hg (by omega) (by omega)
              · by_cases h159 : A.card ≤ 654
                · by_cases h158 : A.card ≤ 642
                  · exact block_157 A h0 hg (by omega) (by omega)
                  · exact block_158 A h0 hg (by omega) (by omega)
                · by_cases h160 : A.card ≤ 666
                  · exact block_159 A h0 hg (by omega) (by omega)
                  · exact block_160 A h0 hg (by omega) (by omega)
          · by_cases h168 : A.card ≤ 693
            · by_cases h164 : A.card ≤ 679
              · by_cases h162 : A.card ≤ 677
                · exact block_161 A h0 hg (by omega) (by omega)
                · by_cases h163 : A.card ≤ 678
                  · exact block_162 A h0 hg (by omega) (by omega)
                  · exact block_163 A h0 hg (by omega) (by omega)
              · by_cases h166 : A.card ≤ 681
                · by_cases h165 : A.card ≤ 680
                  · exact block_164 A h0 hg (by omega) (by omega)
                  · exact block_165 A h0 hg (by omega) (by omega)
                · by_cases h167 : A.card ≤ 682
                  · exact block_166 A h0 hg (by omega) (by omega)
                  · exact block_167 A h0 hg (by omega) (by omega)
            · by_cases h172 : A.card ≤ 726
              · by_cases h170 : A.card ≤ 712
                · by_cases h169 : A.card ≤ 703
                  · exact block_168 A h0 hg (by omega) (by omega)
                  · exact block_169 A h0 hg (by omega) (by omega)
                · by_cases h171 : A.card ≤ 717
                  · exact block_170 A h0 hg (by omega) (by omega)
                  · exact block_171 A h0 hg (by omega) (by omega)
              · by_cases h174 : A.card ≤ 749
                · by_cases h173 : A.card ≤ 739
                  · exact block_172 A h0 hg (by omega) (by omega)
                  · exact block_173 A h0 hg (by omega) (by omega)
                · by_cases h175 : A.card ≤ 760
                  · exact block_174 A h0 hg (by omega) (by omega)
                  · exact block_175 A h0 hg (by omega) (by omega)
      · by_cases h205 : A.card ≤ 1056
        · by_cases h190 : A.card ≤ 891
          · by_cases h183 : A.card ≤ 842
            · by_cases h179 : A.card ≤ 799
              · by_cases h177 : A.card ≤ 779
                · exact block_176 A h0 hg (by omega) (by omega)
                · by_cases h178 : A.card ≤ 790
                  · exact block_177 A h0 hg (by omega) (by omega)
                  · exact block_178 A h0 hg (by omega) (by omega)
              · by_cases h181 : A.card ≤ 824
                · by_cases h180 : A.card ≤ 812
                  · exact block_179 A h0 hg (by omega) (by omega)
                  · exact block_180 A h0 hg (by omega) (by omega)
                · by_cases h182 : A.card ≤ 832
                  · exact block_181 A h0 hg (by omega) (by omega)
                  · exact block_182 A h0 hg (by omega) (by omega)
            · by_cases h186 : A.card ≤ 851
              · by_cases h184 : A.card ≤ 849
                · exact block_183 A h0 hg (by omega) (by omega)
                · by_cases h185 : A.card ≤ 850
                  · exact block_184 A h0 hg (by omega) (by omega)
                  · exact block_185 A h0 hg (by omega) (by omega)
              · by_cases h188 : A.card ≤ 864
                · by_cases h187 : A.card ≤ 852
                  · exact block_186 A h0 hg (by omega) (by omega)
                  · exact block_187 A h0 hg (by omega) (by omega)
                · by_cases h189 : A.card ≤ 876
                  · exact block_188 A h0 hg (by omega) (by omega)
                  · exact block_189 A h0 hg (by omega) (by omega)
          · by_cases h197 : A.card ≤ 959
            · by_cases h193 : A.card ≤ 920
              · by_cases h191 : A.card ≤ 903
                · exact block_190 A h0 hg (by omega) (by omega)
                · by_cases h192 : A.card ≤ 909
                  · exact block_191 A h0 hg (by omega) (by omega)
                  · exact block_192 A h0 hg (by omega) (by omega)
              · by_cases h195 : A.card ≤ 938
                · by_cases h194 : A.card ≤ 930
                  · exact block_193 A h0 hg (by omega) (by omega)
                  · exact block_194 A h0 hg (by omega) (by omega)
                · by_cases h196 : A.card ≤ 951
                  · exact block_195 A h0 hg (by omega) (by omega)
                  · exact block_196 A h0 hg (by omega) (by omega)
            · by_cases h201 : A.card ≤ 1005
              · by_cases h199 : A.card ≤ 982
                · by_cases h198 : A.card ≤ 971
                  · exact block_197 A h0 hg (by omega) (by omega)
                  · exact block_198 A h0 hg (by omega) (by omega)
                · by_cases h200 : A.card ≤ 991
                  · exact block_199 A h0 hg (by omega) (by omega)
                  · exact block_200 A h0 hg (by omega) (by omega)
              · by_cases h203 : A.card ≤ 1030
                · by_cases h202 : A.card ≤ 1017
                  · exact block_201 A h0 hg (by omega) (by omega)
                  · exact block_202 A h0 hg (by omega) (by omega)
                · by_cases h204 : A.card ≤ 1042
                  · exact block_203 A h0 hg (by omega) (by omega)
                  · exact block_204 A h0 hg (by omega) (by omega)
        · by_cases h220 : A.card ≤ 1228
          · by_cases h212 : A.card ≤ 1135
            · by_cases h208 : A.card ≤ 1087
              · by_cases h206 : A.card ≤ 1065
                · exact block_205 A h0 hg (by omega) (by omega)
                · by_cases h207 : A.card ≤ 1080
                  · exact block_206 A h0 hg (by omega) (by omega)
                  · exact block_207 A h0 hg (by omega) (by omega)
              · by_cases h210 : A.card ≤ 1106
                · by_cases h209 : A.card ≤ 1096
                  · exact block_208 A h0 hg (by omega) (by omega)
                  · exact block_209 A h0 hg (by omega) (by omega)
                · by_cases h211 : A.card ≤ 1120
                  · exact block_210 A h0 hg (by omega) (by omega)
                  · exact block_211 A h0 hg (by omega) (by omega)
            · by_cases h216 : A.card ≤ 1172
              · by_cases h214 : A.card ≤ 1151
                · by_cases h213 : A.card ≤ 1142
                  · exact block_212 A h0 hg (by omega) (by omega)
                  · exact block_213 A h0 hg (by omega) (by omega)
                · by_cases h215 : A.card ≤ 1165
                  · exact block_214 A h0 hg (by omega) (by omega)
                  · exact block_215 A h0 hg (by omega) (by omega)
              · by_cases h218 : A.card ≤ 1202
                · by_cases h217 : A.card ≤ 1187
                  · exact block_216 A h0 hg (by omega) (by omega)
                  · exact block_217 A h0 hg (by omega) (by omega)
                · by_cases h219 : A.card ≤ 1216
                  · exact block_218 A h0 hg (by omega) (by omega)
                  · exact block_219 A h0 hg (by omega) (by omega)
          · by_cases h227 : A.card ≤ 1328
            · by_cases h223 : A.card ≤ 1269
              · by_cases h221 : A.card ≤ 1241
                · exact block_220 A h0 hg (by omega) (by omega)
                · by_cases h222 : A.card ≤ 1256
                  · exact block_221 A h0 hg (by omega) (by omega)
                  · exact block_222 A h0 hg (by omega) (by omega)
              · by_cases h225 : A.card ≤ 1296
                · by_cases h224 : A.card ≤ 1278
                  · exact block_223 A h0 hg (by omega) (by omega)
                  · exact block_224 A h0 hg (by omega) (by omega)
                · by_cases h226 : A.card ≤ 1314
                  · exact block_225 A h0 hg (by omega) (by omega)
                  · exact block_226 A h0 hg (by omega) (by omega)
            · by_cases h231 : A.card ≤ 1359
              · by_cases h229 : A.card ≤ 1349
                · by_cases h228 : A.card ≤ 1341
                  · exact block_227 A h0 hg (by omega) (by omega)
                  · exact block_228 A h0 hg (by omega) (by omega)
                · by_cases h230 : A.card ≤ 1356
                  · exact block_229 A h0 hg (by omega) (by omega)
                  · exact block_230 A h0 hg (by omega) (by omega)
              · by_cases h233 : A.card ≤ 1377
                · by_cases h232 : A.card ≤ 1361
                  · exact block_231 A h0 hg (by omega) (by omega)
                  · exact block_232 A h0 hg (by omega) (by omega)
                · by_cases h234 : A.card ≤ 1393
                  · exact block_233 A h0 hg (by omega) (by omega)
                  · exact block_234 A h0 hg (by omega) (by omega)
  · by_cases h352 : A.card ≤ 3558
    · by_cases h293 : A.card ≤ 2322
      · by_cases h264 : A.card ≤ 1800
        · by_cases h249 : A.card ≤ 1604
          · by_cases h242 : A.card ≤ 1504
            · by_cases h238 : A.card ≤ 1447
              · by_cases h236 : A.card ≤ 1419
                · exact block_235 A h0 hg (by omega) (by omega)
                · by_cases h237 : A.card ≤ 1428
                  · exact block_236 A h0 hg (by omega) (by omega)
                  · exact block_237 A h0 hg (by omega) (by omega)
              · by_cases h240 : A.card ≤ 1477
                · by_cases h239 : A.card ≤ 1462
                  · exact block_238 A h0 hg (by omega) (by omega)
                  · exact block_239 A h0 hg (by omega) (by omega)
                · by_cases h241 : A.card ≤ 1488
                  · exact block_240 A h0 hg (by omega) (by omega)
                  · exact block_241 A h0 hg (by omega) (by omega)
            · by_cases h245 : A.card ≤ 1550
              · by_cases h243 : A.card ≤ 1519
                · exact block_242 A h0 hg (by omega) (by omega)
                · by_cases h244 : A.card ≤ 1530
                  · exact block_243 A h0 hg (by omega) (by omega)
                  · exact block_244 A h0 hg (by omega) (by omega)
              · by_cases h247 : A.card ≤ 1580
                · by_cases h246 : A.card ≤ 1564
                  · exact block_245 A h0 hg (by omega) (by omega)
                  · exact block_246 A h0 hg (by omega) (by omega)
                · by_cases h248 : A.card ≤ 1588
                  · exact block_247 A h0 hg (by omega) (by omega)
                  · exact block_248 A h0 hg (by omega) (by omega)
          · by_cases h256 : A.card ≤ 1691
            · by_cases h252 : A.card ≤ 1649
              · by_cases h250 : A.card ≤ 1621
                · exact block_249 A h0 hg (by omega) (by omega)
                · by_cases h251 : A.card ≤ 1634
                  · exact block_250 A h0 hg (by omega) (by omega)
                  · exact block_251 A h0 hg (by omega) (by omega)
              · by_cases h254 : A.card ≤ 1656
                · by_cases h253 : A.card ≤ 1655
                  · exact block_252 A h0 hg (by omega) (by omega)
                  · exact block_253 A h0 hg (by omega) (by omega)
                · by_cases h255 : A.card ≤ 1676
                  · exact block_254 A h0 hg (by omega) (by omega)
                  · exact block_255 A h0 hg (by omega) (by omega)
            · by_cases h260 : A.card ≤ 1745
              · by_cases h258 : A.card ≤ 1716
                · by_cases h257 : A.card ≤ 1701
                  · exact block_256 A h0 hg (by omega) (by omega)
                  · exact block_257 A h0 hg (by omega) (by omega)
                · by_cases h259 : A.card ≤ 1727
                  · exact block_258 A h0 hg (by omega) (by omega)
                  · exact block_259 A h0 hg (by omega) (by omega)
              · by_cases h262 : A.card ≤ 1770
                · by_cases h261 : A.card ≤ 1755
                  · exact block_260 A h0 hg (by omega) (by omega)
                  · exact block_261 A h0 hg (by omega) (by omega)
                · by_cases h263 : A.card ≤ 1785
                  · exact block_262 A h0 hg (by omega) (by omega)
                  · exact block_263 A h0 hg (by omega) (by omega)
        · by_cases h278 : A.card ≤ 2035
          · by_cases h271 : A.card ≤ 1923
            · by_cases h267 : A.card ≤ 1850
              · by_cases h265 : A.card ≤ 1817
                · exact block_264 A h0 hg (by omega) (by omega)
                · by_cases h266 : A.card ≤ 1832
                  · exact block_265 A h0 hg (by omega) (by omega)
                  · exact block_266 A h0 hg (by omega) (by omega)
              · by_cases h269 : A.card ≤ 1891
                · by_cases h268 : A.card ≤ 1870
                  · exact block_267 A h0 hg (by omega) (by omega)
                  · exact block_268 A h0 hg (by omega) (by omega)
                · by_cases h270 : A.card ≤ 1911
                  · exact block_269 A h0 hg (by omega) (by omega)
                  · exact block_270 A h0 hg (by omega) (by omega)
            · by_cases h274 : A.card ≤ 1966
              · by_cases h272 : A.card ≤ 1938
                · exact block_271 A h0 hg (by omega) (by omega)
                · by_cases h273 : A.card ≤ 1953
                  · exact block_272 A h0 hg (by omega) (by omega)
                  · exact block_273 A h0 hg (by omega) (by omega)
              · by_cases h276 : A.card ≤ 1995
                · by_cases h275 : A.card ≤ 1980
                  · exact block_274 A h0 hg (by omega) (by omega)
                  · exact block_275 A h0 hg (by omega) (by omega)
                · by_cases h277 : A.card ≤ 2016
                  · exact block_276 A h0 hg (by omega) (by omega)
                  · exact block_277 A h0 hg (by omega) (by omega)
          · by_cases h285 : A.card ≤ 2171
            · by_cases h281 : A.card ≤ 2089
              · by_cases h279 : A.card ≤ 2051
                · exact block_278 A h0 hg (by omega) (by omega)
                · by_cases h280 : A.card ≤ 2068
                  · exact block_279 A h0 hg (by omega) (by omega)
                  · exact block_280 A h0 hg (by omega) (by omega)
              · by_cases h283 : A.card ≤ 2132
                · by_cases h282 : A.card ≤ 2111
                  · exact block_281 A h0 hg (by omega) (by omega)
                  · exact block_282 A h0 hg (by omega) (by omega)
                · by_cases h284 : A.card ≤ 2153
                  · exact block_283 A h0 hg (by omega) (by omega)
                  · exact block_284 A h0 hg (by omega) (by omega)
            · by_cases h289 : A.card ≤ 2244
              · by_cases h287 : A.card ≤ 2204
                · by_cases h286 : A.card ≤ 2186
                  · exact block_285 A h0 hg (by omega) (by omega)
                  · exact block_286 A h0 hg (by omega) (by omega)
                · by_cases h288 : A.card ≤ 2221
                  · exact block_287 A h0 hg (by omega) (by omega)
                  · exact block_288 A h0 hg (by omega) (by omega)
              · by_cases h291 : A.card ≤ 2282
                · by_cases h290 : A.card ≤ 2265
                  · exact block_289 A h0 hg (by omega) (by omega)
                  · exact block_290 A h0 hg (by omega) (by omega)
                · by_cases h292 : A.card ≤ 2304
                  · exact block_291 A h0 hg (by omega) (by omega)
                  · exact block_292 A h0 hg (by omega) (by omega)
      · by_cases h322 : A.card ≤ 2885
        · by_cases h307 : A.card ≤ 2584
          · by_cases h300 : A.card ≤ 2440
            · by_cases h296 : A.card ≤ 2375
              · by_cases h294 : A.card ≤ 2334
                · exact block_293 A h0 hg (by omega) (by omega)
                · by_cases h295 : A.card ≤ 2355
                  · exact block_294 A h0 hg (by omega) (by omega)
                  · exact block_295 A h0 hg (by omega) (by omega)
              · by_cases h298 : A.card ≤ 2403
                · by_cases h297 : A.card ≤ 2390
                  · exact block_296 A h0 hg (by omega) (by omega)
                  · exact block_297 A h0 hg (by omega) (by omega)
                · by_cases h299 : A.card ≤ 2425
                  · exact block_298 A h0 hg (by omega) (by omega)
                  · exact block_299 A h0 hg (by omega) (by omega)
            · by_cases h303 : A.card ≤ 2503
              · by_cases h301 : A.card ≤ 2463
                · exact block_300 A h0 hg (by omega) (by omega)
                · by_cases h302 : A.card ≤ 2484
                  · exact block_301 A h0 hg (by omega) (by omega)
                  · exact block_302 A h0 hg (by omega) (by omega)
              · by_cases h305 : A.card ≤ 2544
                · by_cases h304 : A.card ≤ 2526
                  · exact block_303 A h0 hg (by omega) (by omega)
                  · exact block_304 A h0 hg (by omega) (by omega)
                · by_cases h306 : A.card ≤ 2568
                  · exact block_305 A h0 hg (by omega) (by omega)
                  · exact block_306 A h0 hg (by omega) (by omega)
          · by_cases h314 : A.card ≤ 2725
            · by_cases h310 : A.card ≤ 2644
              · by_cases h308 : A.card ≤ 2601
                · exact block_307 A h0 hg (by omega) (by omega)
                · by_cases h309 : A.card ≤ 2620
                  · exact block_308 A h0 hg (by omega) (by omega)
                  · exact block_309 A h0 hg (by omega) (by omega)
              · by_cases h312 : A.card ≤ 2687
                · by_cases h311 : A.card ≤ 2662
                  · exact block_310 A h0 hg (by omega) (by omega)
                  · exact block_311 A h0 hg (by omega) (by omega)
                · by_cases h313 : A.card ≤ 2701
                  · exact block_312 A h0 hg (by omega) (by omega)
                  · exact block_313 A h0 hg (by omega) (by omega)
            · by_cases h318 : A.card ≤ 2816
              · by_cases h316 : A.card ≤ 2767
                · by_cases h315 : A.card ≤ 2747
                  · exact block_314 A h0 hg (by omega) (by omega)
                  · exact block_315 A h0 hg (by omega) (by omega)
                · by_cases h317 : A.card ≤ 2791
                  · exact block_316 A h0 hg (by omega) (by omega)
                  · exact block_317 A h0 hg (by omega) (by omega)
              · by_cases h320 : A.card ≤ 2847
                · by_cases h319 : A.card ≤ 2822
                  · exact block_318 A h0 hg (by omega) (by omega)
                  · exact block_319 A h0 hg (by omega) (by omega)
                · by_cases h321 : A.card ≤ 2871
                  · exact block_320 A h0 hg (by omega) (by omega)
                  · exact block_321 A h0 hg (by omega) (by omega)
        · by_cases h337 : A.card ≤ 3214
          · by_cases h329 : A.card ≤ 3020
            · by_cases h325 : A.card ≤ 2946
              · by_cases h323 : A.card ≤ 2901
                · exact block_322 A h0 hg (by omega) (by omega)
                · by_cases h324 : A.card ≤ 2922
                  · exact block_323 A h0 hg (by omega) (by omega)
                  · exact block_324 A h0 hg (by omega) (by omega)
              · by_cases h327 : A.card ≤ 2990
                · by_cases h326 : A.card ≤ 2967
                  · exact block_325 A h0 hg (by omega) (by omega)
                  · exact block_326 A h0 hg (by omega) (by omega)
                · by_cases h328 : A.card ≤ 3003
                  · exact block_327 A h0 hg (by omega) (by omega)
                  · exact block_328 A h0 hg (by omega) (by omega)
            · by_cases h333 : A.card ≤ 3114
              · by_cases h331 : A.card ≤ 3067
                · by_cases h330 : A.card ≤ 3045
                  · exact block_329 A h0 hg (by omega) (by omega)
                  · exact block_330 A h0 hg (by omega) (by omega)
                · by_cases h332 : A.card ≤ 3094
                  · exact block_331 A h0 hg (by omega) (by omega)
                  · exact block_332 A h0 hg (by omega) (by omega)
              · by_cases h335 : A.card ≤ 3163
                · by_cases h334 : A.card ≤ 3138
                  · exact block_333 A h0 hg (by omega) (by omega)
                  · exact block_334 A h0 hg (by omega) (by omega)
                · by_cases h336 : A.card ≤ 3189
                  · exact block_335 A h0 hg (by omega) (by omega)
                  · exact block_336 A h0 hg (by omega) (by omega)
          · by_cases h344 : A.card ≤ 3359
            · by_cases h340 : A.card ≤ 3274
              · by_cases h338 : A.card ≤ 3238
                · exact block_337 A h0 hg (by omega) (by omega)
                · by_cases h339 : A.card ≤ 3253
                  · exact block_338 A h0 hg (by omega) (by omega)
                  · exact block_339 A h0 hg (by omega) (by omega)
              · by_cases h342 : A.card ≤ 3310
                · by_cases h341 : A.card ≤ 3293
                  · exact block_340 A h0 hg (by omega) (by omega)
                  · exact block_341 A h0 hg (by omega) (by omega)
                · by_cases h343 : A.card ≤ 3332
                  · exact block_342 A h0 hg (by omega) (by omega)
                  · exact block_343 A h0 hg (by omega) (by omega)
            · by_cases h348 : A.card ≤ 3449
              · by_cases h346 : A.card ≤ 3410
                · by_cases h345 : A.card ≤ 3388
                  · exact block_344 A h0 hg (by omega) (by omega)
                  · exact block_345 A h0 hg (by omega) (by omega)
                · by_cases h347 : A.card ≤ 3430
                  · exact block_346 A h0 hg (by omega) (by omega)
                  · exact block_347 A h0 hg (by omega) (by omega)
              · by_cases h350 : A.card ≤ 3502
                · by_cases h349 : A.card ≤ 3478
                  · exact block_348 A h0 hg (by omega) (by omega)
                  · exact block_349 A h0 hg (by omega) (by omega)
                · by_cases h351 : A.card ≤ 3530
                  · exact block_350 A h0 hg (by omega) (by omega)
                  · exact block_351 A h0 hg (by omega) (by omega)
    · by_cases h411 : A.card ≤ 5132
      · by_cases h381 : A.card ≤ 4296
        · by_cases h366 : A.card ≤ 3910
          · by_cases h359 : A.card ≤ 3726
            · by_cases h355 : A.card ≤ 3636
              · by_cases h353 : A.card ≤ 3584
                · exact block_352 A h0 hg (by omega) (by omega)
                · by_cases h354 : A.card ≤ 3609
                  · exact block_353 A h0 hg (by omega) (by omega)
                  · exact block_354 A h0 hg (by omega) (by omega)
              · by_cases h357 : A.card ≤ 3678
                · by_cases h356 : A.card ≤ 3656
                  · exact block_355 A h0 hg (by omega) (by omega)
                  · exact block_356 A h0 hg (by omega) (by omega)
                · by_cases h358 : A.card ≤ 3705
                  · exact block_357 A h0 hg (by omega) (by omega)
                  · exact block_358 A h0 hg (by omega) (by omega)
            · by_cases h362 : A.card ≤ 3801
              · by_cases h360 : A.card ≤ 3756
                · exact block_359 A h0 hg (by omega) (by omega)
                · by_cases h361 : A.card ≤ 3775
                  · exact block_360 A h0 hg (by omega) (by omega)
                  · exact block_361 A h0 hg (by omega) (by omega)
              · by_cases h364 : A.card ≤ 3855
                · by_cases h363 : A.card ≤ 3826
                  · exact block_362 A h0 hg (by omega) (by omega)
                  · exact block_363 A h0 hg (by omega) (by omega)
                · by_cases h365 : A.card ≤ 3882
                  · exact block_364 A h0 hg (by omega) (by omega)
                  · exact block_365 A h0 hg (by omega) (by omega)
          · by_cases h373 : A.card ≤ 4090
            · by_cases h369 : A.card ≤ 3984
              · by_cases h367 : A.card ≤ 3939
                · exact block_366 A h0 hg (by omega) (by omega)
                · by_cases h368 : A.card ≤ 3964
                  · exact block_367 A h0 hg (by omega) (by omega)
                  · exact block_368 A h0 hg (by omega) (by omega)
              · by_cases h371 : A.card ≤ 4037
                · by_cases h370 : A.card ≤ 4007
                  · exact block_369 A h0 hg (by omega) (by omega)
                  · exact block_370 A h0 hg (by omega) (by omega)
                · by_cases h372 : A.card ≤ 4061
                  · exact block_371 A h0 hg (by omega) (by omega)
                  · exact block_372 A h0 hg (by omega) (by omega)
            · by_cases h377 : A.card ≤ 4196
              · by_cases h375 : A.card ≤ 4148
                · by_cases h374 : A.card ≤ 4121
                  · exact block_373 A h0 hg (by omega) (by omega)
                  · exact block_374 A h0 hg (by omega) (by omega)
                · by_cases h376 : A.card ≤ 4175
                  · exact block_375 A h0 hg (by omega) (by omega)
                  · exact block_376 A h0 hg (by omega) (by omega)
              · by_cases h379 : A.card ≤ 4247
                · by_cases h378 : A.card ≤ 4216
                  · exact block_377 A h0 hg (by omega) (by omega)
                  · exact block_378 A h0 hg (by omega) (by omega)
                · by_cases h380 : A.card ≤ 4266
                  · exact block_379 A h0 hg (by omega) (by omega)
                  · exact block_380 A h0 hg (by omega) (by omega)
        · by_cases h396 : A.card ≤ 4695
          · by_cases h388 : A.card ≤ 4479
            · by_cases h384 : A.card ≤ 4367
              · by_cases h382 : A.card ≤ 4323
                · exact block_381 A h0 hg (by omega) (by omega)
                · by_cases h383 : A.card ≤ 4337
                  · exact block_382 A h0 hg (by omega) (by omega)
                  · exact block_383 A h0 hg (by omega) (by omega)
              · by_cases h386 : A.card ≤ 4424
                · by_cases h385 : A.card ≤ 4398
                  · exact block_384 A h0 hg (by omega) (by omega)
                  · exact block_385 A h0 hg (by omega) (by omega)
                · by_cases h387 : A.card ≤ 4452
                  · exact block_386 A h0 hg (by omega) (by omega)
                  · exact block_387 A h0 hg (by omega) (by omega)
            · by_cases h392 : A.card ≤ 4579
              · by_cases h390 : A.card ≤ 4519
                · by_cases h389 : A.card ≤ 4503
                  · exact block_388 A h0 hg (by omega) (by omega)
                  · exact block_389 A h0 hg (by omega) (by omega)
                · by_cases h391 : A.card ≤ 4548
                  · exact block_390 A h0 hg (by omega) (by omega)
                  · exact block_391 A h0 hg (by omega) (by omega)
              · by_cases h394 : A.card ≤ 4635
                · by_cases h393 : A.card ≤ 4602
                  · exact block_392 A h0 hg (by omega) (by omega)
                  · exact block_393 A h0 hg (by omega) (by omega)
                · by_cases h395 : A.card ≤ 4662
                  · exact block_394 A h0 hg (by omega) (by omega)
                  · exact block_395 A h0 hg (by omega) (by omega)
          · by_cases h403 : A.card ≤ 4895
            · by_cases h399 : A.card ≤ 4782
              · by_cases h397 : A.card ≤ 4722
                · exact block_396 A h0 hg (by omega) (by omega)
                · by_cases h398 : A.card ≤ 4753
                  · exact block_397 A h0 hg (by omega) (by omega)
                  · exact block_398 A h0 hg (by omega) (by omega)
              · by_cases h401 : A.card ≤ 4835
                · by_cases h400 : A.card ≤ 4810
                  · exact block_399 A h0 hg (by omega) (by omega)
                  · exact block_400 A h0 hg (by omega) (by omega)
                · by_cases h402 : A.card ≤ 4865
                  · exact block_401 A h0 hg (by omega) (by omega)
                  · exact block_402 A h0 hg (by omega) (by omega)
            · by_cases h407 : A.card ≤ 5009
              · by_cases h405 : A.card ≤ 4954
                · by_cases h404 : A.card ≤ 4925
                  · exact block_403 A h0 hg (by omega) (by omega)
                  · exact block_404 A h0 hg (by omega) (by omega)
                · by_cases h406 : A.card ≤ 4985
                  · exact block_405 A h0 hg (by omega) (by omega)
                  · exact block_406 A h0 hg (by omega) (by omega)
              · by_cases h409 : A.card ≤ 5074
                · by_cases h408 : A.card ≤ 5039
                  · exact block_407 A h0 hg (by omega) (by omega)
                  · exact block_408 A h0 hg (by omega) (by omega)
                · by_cases h410 : A.card ≤ 5102
                  · exact block_409 A h0 hg (by omega) (by omega)
                  · exact block_410 A h0 hg (by omega) (by omega)
      · by_cases h440 : A.card ≤ 6000
        · by_cases h425 : A.card ≤ 5550
          · by_cases h418 : A.card ≤ 5342
            · by_cases h414 : A.card ≤ 5220
              · by_cases h412 : A.card ≤ 5159
                · exact block_411 A h0 hg (by omega) (by omega)
                · by_cases h413 : A.card ≤ 5192
                  · exact block_412 A h0 hg (by omega) (by omega)
                  · exact block_413 A h0 hg (by omega) (by omega)
              · by_cases h416 : A.card ≤ 5279
                · by_cases h415 : A.card ≤ 5250
                  · exact block_414 A h0 hg (by omega) (by omega)
                  · exact block_415 A h0 hg (by omega) (by omega)
                · by_cases h417 : A.card ≤ 5315
                  · exact block_416 A h0 hg (by omega) (by omega)
                  · exact block_417 A h0 hg (by omega) (by omega)
            · by_cases h421 : A.card ≤ 5427
              · by_cases h419 : A.card ≤ 5370
                · exact block_418 A h0 hg (by omega) (by omega)
                · by_cases h420 : A.card ≤ 5392
                  · exact block_419 A h0 hg (by omega) (by omega)
                  · exact block_420 A h0 hg (by omega) (by omega)
              · by_cases h423 : A.card ≤ 5491
                · by_cases h422 : A.card ≤ 5460
                  · exact block_421 A h0 hg (by omega) (by omega)
                  · exact block_422 A h0 hg (by omega) (by omega)
                · by_cases h424 : A.card ≤ 5523
                  · exact block_423 A h0 hg (by omega) (by omega)
                  · exact block_424 A h0 hg (by omega) (by omega)
          · by_cases h432 : A.card ≤ 5761
            · by_cases h428 : A.card ≤ 5625
              · by_cases h426 : A.card ≤ 5572
                · exact block_425 A h0 hg (by omega) (by omega)
                · by_cases h427 : A.card ≤ 5602
                  · exact block_426 A h0 hg (by omega) (by omega)
                  · exact block_427 A h0 hg (by omega) (by omega)
              · by_cases h430 : A.card ≤ 5696
                · by_cases h429 : A.card ≤ 5659
                  · exact block_428 A h0 hg (by omega) (by omega)
                  · exact block_429 A h0 hg (by omega) (by omega)
                · by_cases h431 : A.card ≤ 5729
                  · exact block_430 A h0 hg (by omega) (by omega)
                  · exact block_431 A h0 hg (by omega) (by omega)
            · by_cases h436 : A.card ≤ 5882
              · by_cases h434 : A.card ≤ 5813
                · by_cases h433 : A.card ≤ 5789
                  · exact block_432 A h0 hg (by omega) (by omega)
                  · exact block_433 A h0 hg (by omega) (by omega)
                · by_cases h435 : A.card ≤ 5848
                  · exact block_434 A h0 hg (by omega) (by omega)
                  · exact block_435 A h0 hg (by omega) (by omega)
              · by_cases h438 : A.card ≤ 5944
                · by_cases h437 : A.card ≤ 5909
                  · exact block_436 A h0 hg (by omega) (by omega)
                  · exact block_437 A h0 hg (by omega) (by omega)
                · by_cases h439 : A.card ≤ 5972
                  · exact block_438 A h0 hg (by omega) (by omega)
                  · exact block_439 A h0 hg (by omega) (by omega)
        · by_cases h455 : A.card ≤ 6498
          · by_cases h447 : A.card ≤ 6212
            · by_cases h443 : A.card ≤ 6095
              · by_cases h441 : A.card ≤ 6032
                · exact block_440 A h0 hg (by omega) (by omega)
                · by_cases h442 : A.card ≤ 6063
                  · exact block_441 A h0 hg (by omega) (by omega)
                  · exact block_442 A h0 hg (by omega) (by omega)
              · by_cases h445 : A.card ≤ 6159
                · by_cases h444 : A.card ≤ 6120
                  · exact block_443 A h0 hg (by omega) (by omega)
                  · exact block_444 A h0 hg (by omega) (by omega)
                · by_cases h446 : A.card ≤ 6189
                  · exact block_445 A h0 hg (by omega) (by omega)
                  · exact block_446 A h0 hg (by omega) (by omega)
            · by_cases h451 : A.card ≤ 6363
              · by_cases h449 : A.card ≤ 6288
                · by_cases h448 : A.card ≤ 6249
                  · exact block_447 A h0 hg (by omega) (by omega)
                  · exact block_448 A h0 hg (by omega) (by omega)
                · by_cases h450 : A.card ≤ 6324
                  · exact block_449 A h0 hg (by omega) (by omega)
                  · exact block_450 A h0 hg (by omega) (by omega)
              · by_cases h453 : A.card ≤ 6435
                · by_cases h452 : A.card ≤ 6400
                  · exact block_451 A h0 hg (by omega) (by omega)
                  · exact block_452 A h0 hg (by omega) (by omega)
                · by_cases h454 : A.card ≤ 6466
                  · exact block_453 A h0 hg (by omega) (by omega)
                  · exact block_454 A h0 hg (by omega) (by omega)
          · by_cases h462 : A.card ≤ 6740
            · by_cases h458 : A.card ≤ 6604
              · by_cases h456 : A.card ≤ 6531
                · exact block_455 A h0 hg (by omega) (by omega)
                · by_cases h457 : A.card ≤ 6564
                  · exact block_456 A h0 hg (by omega) (by omega)
                  · exact block_457 A h0 hg (by omega) (by omega)
              · by_cases h460 : A.card ≤ 6665
                · by_cases h459 : A.card ≤ 6634
                  · exact block_458 A h0 hg (by omega) (by omega)
                  · exact block_459 A h0 hg (by omega) (by omega)
                · by_cases h461 : A.card ≤ 6704
                  · exact block_460 A h0 hg (by omega) (by omega)
                  · exact block_461 A h0 hg (by omega) (by omega)
            · by_cases h466 : A.card ≤ 6886
              · by_cases h464 : A.card ≤ 6817
                · by_cases h463 : A.card ≤ 6779
                  · exact block_462 A h0 hg (by omega) (by omega)
                  · exact block_463 A h0 hg (by omega) (by omega)
                · by_cases h465 : A.card ≤ 6850
                  · exact block_464 A h0 hg (by omega) (by omega)
                  · exact block_465 A h0 hg (by omega) (by omega)
              · by_cases h468 : A.card ≤ 6957
                · by_cases h467 : A.card ≤ 6922
                  · exact block_466 A h0 hg (by omega) (by omega)
                  · exact block_467 A h0 hg (by omega) (by omega)
                · by_cases h469 : A.card ≤ 6995
                  · exact block_468 A h0 hg (by omega) (by omega)
                  · exact block_469 A h0 hg (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem finite_bound (A : Finset ℕ) (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hc : A.card ≤ 7000) : GrahamBound A := by
  by_cases hs : A.card ≤ 10
  · exact grahamBound_of_card_le_ten A h0 hne hs
  apply grahamBound_of_normalize A
  have hbc := normalize_card A
  exact finite_normalized_core (normalize A) (normalize_nonzero A h0)
    (normalize_gcd A h0 hne) (by omega) (by omega)
end OMA.GrahamFinite

theorem OMA.solution : OMA.R_Erdos402_erdos_402_R2.H1 := by
  intro A h0 _hg h4 h7000 _hp _hsq _hd _hsmooth
  exact OMA.GrahamFinite.finite_bound A h0 (Finset.card_pos.mp (by omega)) h7000
