import OMAStatements.S_mo_301110

/-!
A finite counting proof of Kalmynin's obstruction for the Klarner–Rado orbit
(arXiv:2611.22034). Rational itineraries furnish words with a common power of two
in their slopes. A finite cut of the word tree then bounds how many orbit points
can come from those words and forces a strict decrease in any near-optimal density bound.
-/

namespace KlarnerWords

inductive Step | twice | triple | six
  deriving DecidableEq

open Step

private def exp₂ : Step → ℕ
  | twice | six => 1
  | triple => 0

private def exp₃ : Step → ℕ
  | triple | six => 1
  | twice => 0

private def shift : Step → ℕ
  | twice => 0
  | triple => 2
  | six => 3

abbrev Word := List Step

def twos (w : Word) : ℕ := (w.map exp₂).sum

def threes (w : Word) : ℕ := (w.map exp₃).sum

def slope (w : Word) : ℕ := 2 ^ (twos w) * 3 ^ (threes w)

def offset : Word → ℕ
  | [] => 0
  | s :: w => slope [s] * offset w + shift s

def action (w : Word) (x : ℚ) : ℚ := (slope w : ℚ) * x + offset w

def run (w : Word) (x : ℕ) : ℕ := slope w * x + offset w

@[simp] theorem twos_append (w v : Word) : twos (w ++ v) = twos w + twos v := by
  simp [twos]

@[simp] theorem threes_append (w v : Word) : threes (w ++ v) = threes w + threes v := by
  simp [threes]

@[simp] theorem slope_append (w v : Word) : slope (w ++ v) = slope w * slope v := by
  simp [slope, pow_add]
  ring

@[simp] theorem slope_nil : slope [] = 1 := by simp [slope, twos, threes]

@[simp] theorem slope_pos (w : Word) : 0 < slope w := by unfold slope; positivity

theorem offset_append (w v : Word) : offset (w ++ v) = slope w * offset v + offset w := by
  induction w with
  | nil => simp [offset]
  | cons s w ih =>
    change slope [s] * offset (w ++ v) + shift s = slope (s :: w) * offset v +
      (slope [s] * offset w + shift s)
    rw [ih, show s :: w = [s] ++ w from rfl, slope_append]; ring

@[simp] theorem action_append (w v : Word) (x : ℚ) : action (w ++ v) x = action w (action v x) := by
  simp [action, offset_append]; ring

@[simp] theorem run_append (w v : Word) (x : ℕ) : run (w ++ v) x = run w (run v x) := by
  simp [run, offset_append]; ring

@[simp] theorem action_twice (x : ℚ) : action [twice] x = 2*x := by
  norm_num [action, offset, slope, twos, threes, exp₂, exp₃, shift]

@[simp] theorem action_triple (x : ℚ) : action [triple] x = 3*x+2 := by
  norm_num [action, offset, slope, twos, threes, exp₂, exp₃, shift]

@[simp] theorem action_six (x : ℚ) : action [six] x = 6*x+3 := by
  norm_num [action, offset, slope, twos, threes, exp₂, exp₃, shift]

/-- Every reduced denominator `3^m` in the open unit interval has an orbit to zero. -/
theorem escape (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hlt : k < 3^m) (hnd : ¬ 3 ∣ k) :
    ∃ w : Word, w.head? ≠ some twice ∧ threes w = m ∧
      action w (-(k : ℚ) / (3 : ℚ)^m) = 0 := by
  induction hmeasure : (3^m + (3^m-k) : ℕ) using Nat.strong_induction_on generalizing m k with
  | h measure ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    cases j with
    | zero =>
      norm_num at hlt
      interval_cases k
      · exact ⟨[triple, twice], by decide, by decide, by
          rw [show [triple, twice] = [triple] ++ [twice] by rfl, action_append]
          norm_num⟩
      · exact ⟨[triple], by decide, by decide, by norm_num⟩
    | succ j =>
      let p : ℕ := 3 ^ (j + 1)
      have hp : 0 < p := by dsimp [p]; positivity
      have hpow : 3 ^ (j + 1 + 1) = 3*p := by simp [p, pow_succ, Nat.mul_comm]
      have hpmod : p % 3 = 0 := by simp [p, pow_succ]
      rw [hpow] at hlt hmeasure
      change 3 * p + (3 * p - k) = measure at hmeasure
      by_cases hd : 2*k < 3*p
      · have hnext : 3^(j+1+1) + (3^(j+1+1)-2*k) < measure := by rw [hpow, ← hmeasure]; omega
        have hlt' : 2*k < 3^(j+1+1) := hpow ▸ hd
        have hnd' : ¬3 ∣ 2*k := by omega
        obtain ⟨w, hw, hw₃, hz⟩ :=
          ih _ hnext (j+1+1) (2*k) (by omega) (by omega) hlt' hnd' rfl
        have hn : w ≠ [] := by intro hz'; subst w; simp [threes] at hw₃
        refine ⟨w ++ [twice], ?_, by simpa [threes, exp₃] using hw₃, ?_⟩
        · cases w with
          | nil => contradiction
          | cons s w => simpa using hw
        · rw [action_append, action_twice]
          convert hz using 2
          push_cast
          simp only [Nat.succ_eq_add_one]
          ring
      · by_cases hb : 2*p ≤ k
        · have hkp : 2*p < k := by
            by_contra! hle
            have heq : k = 2*p := by omega
            omega
          let q : ℕ := k - 2*p
          have hq : 0 < q := by dsimp [q]; omega
          have hq' : q < p := by dsimp [q]; omega
          have hnd' : ¬3 ∣ q := by dsimp [q]; omega
          have hnext : p + (p-q) < measure := by rw [← hmeasure]; omega
          obtain ⟨w, hw, hw₃, hz⟩ :=
            ih _ hnext (j+1) q (by omega) hq hq' hnd' rfl
          have hn : w ≠ [] := by intro hz'; subst w; simp [threes] at hw₃
          refine ⟨w ++ [triple], ?_, by rw [threes_append, hw₃]; rfl, ?_⟩
          · cases w with
            | nil => contradiction
            | cons s w => simpa using hw
          · rw [action_append, action_triple]
            convert hz using 2
            push_cast [q, Nat.cast_sub hb, p]
            simp only [Nat.succ_eq_add_one, pow_succ]
            have : (3 : ℚ) ^ (j+1) ≠ 0 := by positivity
            field_simp
            ring
        · have hkp : 3*p < 2*k := by
            by_contra! hle
            have heq : 2*k = 3*p := by omega
            omega
          let q : ℕ := 2*k - 3*p
          have hq : 0 < q := by dsimp [q]; omega
          have hq' : q < p := by dsimp [q]; omega
          have hnd' : ¬3 ∣ q := by dsimp [q]; omega
          have hnext : p + (p-q) < measure := by rw [← hmeasure]; omega
          obtain ⟨w, hw, hw₃, hz⟩ :=
            ih _ hnext (j+1) q (by omega) hq hq' hnd' rfl
          have hn : w ≠ [] := by intro hz'; subst w; simp [threes] at hw₃
          refine ⟨w ++ [six], ?_, by rw [threes_append, hw₃]; rfl, ?_⟩
          · cases w with
            | nil => contradiction
            | cons s w => simpa using hw
          · rw [action_append, action_six]
            convert hz using 2
            push_cast [q, Nat.cast_sub hkp.le, p]
            simp only [Nat.succ_eq_add_one, pow_succ]
            have : (3 : ℚ) ^ (j+1) ≠ 0 := by positivity
            field_simp
            ring

@[simp] theorem run_nil (x : ℕ) : run [] x = x := by simp [run, offset]

@[simp] theorem run_twice (x : ℕ) : run [twice] x = 2*x := by
  norm_num [run, offset, slope, twos, threes, exp₂, exp₃, shift]

@[simp] theorem run_triple (x : ℕ) : run [triple] x = 3*x+2 := by
  norm_num [run, offset, slope, twos, threes, exp₂, exp₃, shift]

@[simp] theorem run_six (x : ℕ) : run [six] x = 6*x+3 := by
  norm_num [run, offset, slope, twos, threes, exp₂, exp₃, shift]

@[simp] theorem twos_repeat (n : ℕ) : twos (List.replicate n twice) = n := by
  simp [twos, exp₂]

@[simp] theorem threes_repeat (n : ℕ) : threes (List.replicate n twice) = 0 := by
  simp [threes, exp₃]

@[simp] theorem action_repeat (n : ℕ) : action (List.replicate n twice) 0 = 0 := by
  induction n with
  | zero => simp [action, offset]
  | succ n ih =>
    rw [List.replicate_succ, show twice :: List.replicate n twice = [twice] ++ List.replicate n twice
      from rfl, action_append, ih, action_twice, mul_zero]

theorem offset_of_zero {w : Word} {m k : ℕ} (hm : threes w = m)
    (hw : action w (-(k : ℚ) / (3 : ℚ)^m) = 0) : offset w = 2^(twos w) * k := by
  rw [action, slope, hm] at hw
  push_cast at hw
  have hpow : (3:ℚ)^m ≠ 0 := by positivity
  have h : ((offset w : ℕ) : ℚ) = (2:ℚ)^twos w * (k:ℚ) := by
    field_simp at hw
    linarith
  exact_mod_cast h

end KlarnerWords

namespace KlarnerWords
open Step
open Finset
open scoped BigOperators

private def consEmb (s : Step) : Word ↪ Word :=
  ⟨List.cons s, fun _ _ h => (List.cons.inj h).2⟩

def leaves : ℕ → ℕ → Finset Word
  | _, 0 => {[]}
  | 0, _ + 1 => {[]}
  | n+1, D+1 =>
    ((leaves n D).map (consEmb twice) ∪ (leaves (n+1) D).map (consEmb triple)) ∪
      (leaves n D).map (consEmb six)

private theorem prefix_disjoint {s t : Step} (hst : s ≠ t)
    (A B : Finset Word) : Disjoint (A.map (consEmb s)) (B.map (consEmb t)) := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hw
  obtain ⟨y, hy, h⟩ := Finset.mem_map.mp hw'
  change t :: y = s :: x at h
  exact hst (List.cons.inj h).1.symm

private theorem slope_step_twice : slope [twice] = 2 := by decide
private theorem slope_step_triple : slope [triple] = 3 := by decide
private theorem slope_step_six : slope [six] = 6 := by decide

private theorem sum_prefix_weight (s : Step) (A : Finset Word) :
    (∑ w ∈ A.map (consEmb s), (1 : ℝ) / slope w) =
      ((1 : ℝ) / slope [s]) * ∑ w ∈ A, (1 : ℝ) / slope w := by
  rw [Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  change (1 : ℝ) / slope (s :: w) = _
  rw [show s :: w = [s] ++ w from rfl, slope_append, Nat.cast_mul]
  rw [one_div_mul_one_div]

theorem sum_leaves_weight (n D : ℕ) :
    (∑ w ∈ leaves n D, (1 : ℝ) / slope w) = 1 := by
  induction D generalizing n with
  | zero => simp [leaves]
  | succ D ih =>
    cases n with
    | zero => simp [leaves]
    | succ n =>
      rw [leaves, Finset.sum_union, Finset.sum_union]
      · simp only [sum_prefix_weight, ih, slope_step_twice, slope_step_triple, slope_step_six]
        norm_num
      · exact prefix_disjoint (by decide) _ _
      · exact disjoint_sup_left.mpr
          ⟨prefix_disjoint (by decide) _ _, prefix_disjoint (by decide) _ _⟩

theorem leaves_factor (n D : ℕ) (w : Word) (h : D ≤ w.length) :
    ∃ u ∈ leaves n D, ∃ v, w = u ++ v := by
  induction D generalizing n w with
  | zero => exact ⟨[], by simp [leaves], w, rfl⟩
  | succ D ih =>
    cases n with
    | zero => exact ⟨[], by simp [leaves], w, rfl⟩
    | succ n =>
      cases w with
      | nil => simp at h
      | cons s w =>
        have h' : D ≤ w.length := by simpa using h
        cases s with
        | twice =>
          obtain ⟨u, hu, v, rfl⟩ := ih n w h'
          exact ⟨twice :: u, by
            rw [leaves]; exact mem_union_left _ (mem_union_left _ (mem_map.mpr ⟨u,hu,rfl⟩)),
            v, rfl⟩
        | triple =>
          obtain ⟨u, hu, v, rfl⟩ := ih (n+1) w h'
          exact ⟨triple :: u, by
            rw [leaves]; exact mem_union_left _ (mem_union_right _ (mem_map.mpr ⟨u,hu,rfl⟩)),
            v, rfl⟩
        | six =>
          obtain ⟨u, hu, v, rfl⟩ := ih n w h'
          exact ⟨six :: u, by
            rw [leaves]; exact mem_union_right _ (mem_map.mpr ⟨u,hu,rfl⟩),
            v, rfl⟩

private theorem twos_nil : twos [] = 0 := by decide

private theorem twos_cons (s : Step) (w : Word) :
    twos (s :: w) = exp₂ s + twos w := by simp [twos]

private theorem snd_last {w : Word} {s : Step} (h : w.getLast? = some s) :
    ∃ u, w = u ++ [s] := by
  induction w with
  | nil => simp at h
  | cons t w ih =>
    cases w with
    | nil => simp at h; subst t; exact ⟨[], rfl⟩
    | cons u w =>
      have h' : (u :: w).getLast? = some s := by simpa only [List.getLast?_cons_cons] using h
      obtain ⟨v, hv⟩ := ih h'
      exact ⟨t :: v, by rw [List.cons_append, ← hv]⟩

private theorem twos_pos_of_ending {w : Word}
    (he : w.getLast? = some twice ∨ w.getLast? = some six) : 0 < twos w := by
  rcases he with he | he <;> obtain ⟨u, rfl⟩ := snd_last he <;>
    simp [twos, exp₂]

private theorem last_valid_tail (s : Step) (w : Word)
    (h : (s :: w).getLast? = some twice ∨ (s :: w).getLast? = some six) :
    w = [] ∨ w.getLast? = some twice ∨ w.getLast? = some six := by
  cases w with
  | nil => exact Or.inl rfl
  | cons t w => exact Or.inr (by simpa only [List.getLast?_cons_cons] using h)

theorem leaves_mem_of_ending (n D : ℕ) (w : Word) (hD : w.length ≤ D)
    (ht : twos w = n)
    (he : w = [] ∨ w.getLast? = some twice ∨ w.getLast? = some six) :
    w ∈ leaves n D := by
  induction D generalizing n w with
  | zero =>
    have : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    simp [leaves]
  | succ D ih =>
    cases n with
    | zero =>
      rcases he with rfl | he
      · simp [leaves]
      · have := twos_pos_of_ending he
        omega
    | succ n =>
      cases w with
      | nil => rw [twos_nil] at ht; omega
      | cons s w =>
        have h' : w.length ≤ D := by simpa using hD
        have he' := last_valid_tail s w (he.resolve_left (by simp))
        rw [twos_cons] at ht
        cases s with
        | twice =>
          have ht' : twos w = n := by simp [exp₂] at ht; omega
          rw [leaves]
          exact mem_union_left _ (mem_union_left _ (mem_map.mpr ⟨w, ih n w h' ht' he', rfl⟩))
        | triple =>
          have ht' : twos w = n+1 := by simpa [exp₂] using ht
          rw [leaves]
          exact mem_union_left _ (mem_union_right _ (mem_map.mpr ⟨w, ih (n+1) w h' ht' he', rfl⟩))
        | six =>
          have ht' : twos w = n := by simp [exp₂] at ht; omega
          rw [leaves]
          exact mem_union_right _ (mem_map.mpr ⟨w, ih n w h' ht' he', rfl⟩)

end KlarnerWords

namespace KlarnerWords
open Step Finset

private theorem nice_seed (m : ℕ) (j : Fin (3^m)) :
    ∃ w : Word, threes w = m+2 ∧ w.getLast? = some twice ∧
      action w (-((3*j.val+1 : ℕ) : ℚ) / (3:ℚ)^(m+2)) = 0 := by
  have hj := j.isLt
  have hlt : 2*(3*j.val+1) < 3^(m+2) := by rw [pow_add, show (3:ℕ)^2 = 9 by decide]; omega
  obtain ⟨w, _, h3, hz⟩ := escape (m+2) (2*(3*j.val+1)) (by omega) (by omega) hlt (by omega)
  refine ⟨w ++ [twice], ?_, by simp, ?_⟩
  · rw [threes_append, h3]; rfl
  · rw [action_append, action_twice]
    convert hz using 2
    push_cast
    ring

private noncomputable def seed {M : ℕ} (i : Σ m : Fin M, Fin (3^m.val)) : Word :=
  (nice_seed i.1.val i.2).choose

private theorem seed_spec {M : ℕ} (i : Σ m : Fin M, Fin (3^m.val)) :
    threes (seed i) = i.1.val+2 ∧ (seed i).getLast? = some twice ∧
      action (seed i) (-((3*i.2.val+1 : ℕ) : ℚ) / (3:ℚ)^(i.1.val+2)) = 0 :=
  (nice_seed i.1.val i.2).choose_spec

private noncomputable def pad {M : ℕ} (n : ℕ) (i : Σ m : Fin M, Fin (3^m.val)) : Word :=
  List.replicate (n-twos (seed i)) twice ++ seed i

private theorem pad_twos {M n : ℕ} (i : Σ m : Fin M, Fin (3^m.val))
    (h : twos (seed i) ≤ n) : twos (pad n i) = n := by
  simp [pad, Nat.sub_add_cancel h]

private theorem pad_threes {M : ℕ} (n : ℕ) (i : Σ m : Fin M, Fin (3^m.val)) :
    threes (pad n i) = i.1.val+2 := by simp [pad, (seed_spec i).1]

private theorem pad_last {M : ℕ} (n : ℕ) (i : Σ m : Fin M, Fin (3^m.val)) :
    (pad n i).getLast? = some twice := by
  simp [pad, List.getLast?_append, (seed_spec i).2.1]

private theorem pad_offset {M n : ℕ} (i : Σ m : Fin M, Fin (3^m.val))
    (h : twos (seed i) ≤ n) : offset (pad n i) = 2^n * (3*i.2.val+1) := by
  have hz : action (pad n i) (-((3*i.2.val+1 : ℕ) : ℚ) / (3:ℚ)^(i.1.val+2)) = 0 := by
    rw [pad, action_append, (seed_spec i).2.2, action_repeat]
  rw [offset_of_zero (pad_threes n i) hz, pad_twos i h]

private theorem pad_injective {M n : ℕ} (h : ∀ i : Σ m : Fin M, Fin (3^m.val), twos (seed i) ≤ n) :
    Function.Injective (pad n (M := M)) := by
  rintro ⟨m,i⟩ ⟨k,j⟩ hij
  have hmk : m = k := by
    have e := congrArg threes hij
    rw [pad_threes, pad_threes] at e
    exact Fin.ext (by simp at e; omega)
  subst k
  have e := congrArg offset hij
  rw [pad_offset _ (h _), pad_offset _ (h _)] at e
  have hpow : 0 < 2^n := by positivity
  have e' := Nat.eq_of_mul_eq_mul_left hpow e
  congr 1
  exact Fin.ext (by simp at e'; omega)

/-- A finite family of words with a fixed power of two in the slope. -/
theorem nice_family (M : ℕ) :
    ∃ (n D : ℕ) (G : Finset Word), 0 < n ∧
      (∀ w ∈ G, w.length ≤ D ∧ twos w = n ∧ w.getLast? = some twice ∧ 2^n ∣ offset w) ∧
      (∑ w ∈ G, (1:ℝ) / slope w) = (M:ℝ) / (9 * 2^n) := by
  classical
  let I := Σ m : Fin M, Fin (3^m.val)
  let n := 1 + (Finset.univ : Finset I).sup (fun i => twos (seed i))
  have hn (i : I) : twos (seed i) ≤ n := by
    exact (Finset.le_sup (f := fun j : I => twos (seed j)) (Finset.mem_univ i)).trans (by dsimp [n]; omega)
  let D := (Finset.univ : Finset I).sup (fun i => (pad n i).length)
  let G := (Finset.univ : Finset I).image (pad n)
  refine ⟨n,D,G,by dsimp [n]; omega,?_,?_⟩
  · intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    refine ⟨Finset.le_sup (f := fun j : I => (pad n j).length) (Finset.mem_univ i),
      pad_twos i (hn i), pad_last n i, ?_⟩
    exact ⟨3*i.2.val+1, pad_offset i (hn i)⟩
  · rw [show G = (Finset.univ : Finset I).image (pad n) from rfl, Finset.sum_image
      (fun _ _ _ _ e => pad_injective hn e)]
    change (∑ i : Σ m : Fin M, Fin (3^m.val), (1:ℝ) / slope (pad n i)) = _
    rw [Fintype.sum_sigma]
    calc
      (∑ i : Fin M, ∑ j : Fin (3^i.val), (1:ℝ) / slope (pad n ⟨i,j⟩)) =
          ∑ _ : Fin M, (1:ℝ)/(9*2^n) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [slope, pad_twos _ (hn _), pad_threes, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [pow_add]
        field_simp
        ring
      _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]

end KlarnerWords

namespace KlarnerWords

open Filter Finset
open scoped BigOperators

theorem finite_density_contradiction {ι : Type*} (A : ℕ → ℕ) (bad : Finset ι)
    (a : ι → ℕ) (ha : ∀ i ∈ bad, 0 < a i)
    (d q K : ℝ) (hd : 0 < d)
    (hA : ∀ x, A x ≤ x + 1)
    (hlo : ∀ᶠ x : ℕ in atTop, d * x ≤ (A x : ℝ))
    (hweight : (∑ i ∈ bad, (1 : ℝ) / a i) ≤ 1)
    (hgap : q < d * (1 - ∑ i ∈ bad, (1 : ℝ) / a i))
    (hrec : ∀ᶠ x : ℕ in atTop,
      (A x : ℝ) ≤ K + q * x + ∑ i ∈ bad, (A (x / a i) : ℝ)) :
    False := by
  let good : Set ℝ := {b | ∀ᶠ x : ℕ in atTop, (A x : ℝ) ≤ b * x}
  have hnonempty : good.Nonempty := by
    refine ⟨2, eventually_atTop.mpr ⟨1, fun x hx => ?_⟩⟩
    have h₁ : (A x : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast hA x
    have h₂ : (1 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hbelow {b : ℝ} (hb : b ∈ good) : d ≤ b := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlo.and hb)
    obtain ⟨h₁, h₂⟩ := hN (N + 1) (by omega)
    exact le_of_mul_le_mul_right (h₁.trans h₂) (by positivity)
  have hbounded : BddBelow good := ⟨d, fun _ hb => hbelow hb⟩
  let W : ℝ := ∑ i ∈ bad, (1 : ℝ) / a i
  let δ : ℝ := (d * (1 - W) - q) / 2
  have hδ : 0 < δ := by dsimp [δ, W]; linarith
  obtain ⟨b, hb, hbclose⟩ := exists_lt_of_csInf_lt hnonempty
    (show sInf good < sInf good + δ by linarith)
  have hdb := hbelow hb
  have hbpos : 0 ≤ b := by linarith
  have hbscaled : ∀ᶠ x : ℕ in atTop, ∀ i ∈ bad, (A (x / a i) : ℝ) ≤ b * (x / (a i : ℝ)) := by
    rw [eventually_all_finset]
    intro i hi
    obtain ⟨N, hN⟩ := eventually_atTop.mp hb
    refine eventually_atTop.mpr ⟨N * a i, fun x hx => ?_⟩
    have hi0 : (0 : ℝ) < a i := by exact_mod_cast ha i hi
    have hxd : N ≤ x / a i := (Nat.le_div_iff_mul_le (ha i hi)).2 hx
    have hfloor : ((x / a i : ℕ) : ℝ) ≤ (x : ℝ) / a i := by
      apply (le_div_iff₀ hi0).2
      exact_mod_cast Nat.div_mul_le_self x (a i)
    exact (hN _ hxd).trans (mul_le_mul_of_nonneg_left hfloor hbpos)
  have hKe : ∀ᶠ x : ℕ in atTop, K ≤ δ * x := by
    obtain ⟨N, hN⟩ := exists_nat_gt (K / δ)
    refine eventually_atTop.mpr ⟨N, fun x hx => ?_⟩
    have hcast : (N : ℝ) ≤ x := by exact_mod_cast hx
    have ht := (div_lt_iff₀ hδ).1 hN
    calc
      K ≤ (N : ℝ) * δ := ht.le
      _ ≤ (x : ℝ) * δ := mul_le_mul_of_nonneg_right hcast hδ.le
      _ = δ * x := mul_comm _ _
  have himprove : b - δ ∈ good := by
    filter_upwards [hrec, hbscaled, hKe] with x hxr hxs hxK
    have hsum : (∑ i ∈ bad, (A (x / a i) : ℝ)) ≤ b * x * W := by
      calc
        _ ≤ ∑ i ∈ bad, b * ((x : ℝ) / a i) := Finset.sum_le_sum hxs
        _ = b * x * W := by
          dsimp [W]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    have hm : 0 ≤ (b - d) * (1 - W) := by
      apply mul_nonneg (sub_nonneg.mpr hdb)
      exact sub_nonneg.mpr hweight
    have hcoeff : δ + q + b * W ≤ b - δ := by
      dsimp [δ]
      linarith only [hm]
    calc
      (A x : ℝ) ≤ K + q * x + ∑ i ∈ bad, (A (x / a i) : ℝ) := hxr
      _ ≤ δ*x + q*x + b*x*W := by linarith
      _ = (δ + q + b*W) * x := by ring
      _ ≤ (b - δ) * x := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hmin := csInf_le hbounded himprove
  linarith only [hmin, hbclose]

end KlarnerWords

namespace KlarnerWords
open Step OMA.S_mo_301110

private theorem from_word (w : Word) : InKR (run w 1) := by
  induction w with
  | nil => simpa using InKR.one
  | cons s w ih =>
    rw [show s :: w = [s] ++ w by rfl, run_append]
    cases s with
    | twice => simpa using InKR.double ih
    | triple => simpa using InKR.three ih
    | six => simpa using InKR.six ih

private theorem to_word {n : ℕ} (h : InKR n) : ∃ w : Word, run w 1 = n := by
  induction h with
  | one => exact ⟨[], run_nil _⟩
  | double h ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨[twice]++w, by rw [run_append, run_twice, hw]⟩
  | three h ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨[triple]++w, by rw [run_append, run_triple, hw]⟩
  | six h ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨[six]++w, by rw [run_append, run_six, hw]⟩

private theorem run_pos (w : Word) : 0 < run w 1 := by
  change 0 < slope w * 1 + offset w
  rw [mul_one]
  exact (slope_pos w).trans_le (Nat.le_add_right _ (offset w))

private theorem run_small (w : Word) : run w 1 < 9^(w.length+1) := by
  induction w with
  | nil => norm_num
  | cons s w ih =>
    have hpos := run_pos w
    have hle : run [s] (run w 1) ≤ 9 * run w 1 := by
      cases s <;> simp <;> omega
    rw [show s :: w = [s] ++ w by rfl, run_append]
    change run [s] (run w 1) < 9^(w.length+1+1)
    rw [pow_succ, mul_comm]
    exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left ih (by decide))

open Classical in
private noncomputable def points (x : ℕ) : Finset ℕ := (Finset.range (x+1)).filter InKR

noncomputable def population (x : ℕ) : ℕ := (points x).card

private theorem mem_points {x t : ℕ} : t ∈ points x ↔ t ≤ x ∧ InKR t := by
  simp [points]

theorem population_eq_ncard (x : ℕ) : population x = Set.ncard {n : ℕ | n ≤ x ∧ InKR n} := by
  rw [population, ← Set.ncard_coe_finset]
  congr 1
  ext n
  exact mem_points

theorem population_le (x : ℕ) : population x ≤ x+1 := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

private theorem run_mul_bound {w : Word} {t x : ℕ} (h : run w t ≤ x) :
    t ≤ x / slope w := by
  apply (Nat.le_div_iff_mul_le (slope_pos w)).mpr
  rw [Nat.mul_comm]
  exact (Nat.le_add_right _ _).trans h

private theorem good_run_dvd {w : Word} {n t : ℕ} (ht : twos w = n)
    (ho : 2^n ∣ offset w) : 2^n ∣ run w t := by
  rw [run, slope, ht]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) ho

theorem population_bound {n D : ℕ} {G : Finset Word}
    (hG : ∀ w ∈ G, twos w = n ∧ 2^n ∣ offset w) (x : ℕ) :
    population x ≤ (9^(D+1)+1) + x / (2^n) +
      ∑ w ∈ leaves n D \ G, population (x / slope w) := by
  classical
  let T := 9^(D+1)
  let p := 2^n
  have hp : 0 < p := by dsimp [p]; positivity
  let multiples := (Finset.range (x / p + 1)).image (fun j => p*j)
  let bad := leaves n D \ G
  let img := fun w => (points (x/slope w)).image (run w)
  have hcover : points x ⊆ (Finset.range T ∪ multiples) ∪ bad.biUnion img := by
    intro k hk
    have h := mem_points.mp hk
    obtain ⟨w, rfl⟩ := to_word h.2
    by_cases hw : w.length < D
    · have hsmall : run w 1 < T :=
        (run_small w).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hsmall))
    · obtain ⟨u, hu, v, rfl⟩ := leaves_factor n D w (by omega)
      rw [run_append] at h ⊢
      by_cases hg : u ∈ G
      · have hg' := hG u hg
        obtain ⟨q, hq⟩ := good_run_dvd (t := run v 1) hg'.1 hg'.2
        have hq' : q ≤ x / p := by
          apply (Nat.le_div_iff_mul_le hp).2
          rw [mul_comm, ← hq]
          exact h.1
        refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ?_))
        exact ⟨q, Finset.mem_range.mpr (by omega), hq.symm⟩
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu,hg⟩, ?_⟩)
        exact Finset.mem_image.mpr ⟨run v 1,
          mem_points.mpr ⟨run_mul_bound h.1, from_word v⟩, rfl⟩
  have hmult : multiples.card ≤ x/p+1 := Finset.card_image_le.trans_eq (Finset.card_range _)
  have hbad : (bad.biUnion img).card ≤ ∑ w ∈ bad, population (x/slope w) := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ => ?_)
    exact Finset.card_image_le
  have hunion := Finset.card_union_le (Finset.range T ∪ multiples) (bad.biUnion img)
  have hadd := Finset.card_union_le (Finset.range T) multiples
  rw [Finset.card_range] at hadd
  have hcard := Finset.card_le_card hcover
  change (points x).card ≤ T+1+x/p+∑ w ∈ bad, population (x/slope w)
  omega

end KlarnerWords

open Filter KlarnerWords

/-- Kalmynin's orbit obstruction, using a finite word cut and counting on ℕ. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_301110.main) := by
  classical
  rintro ⟨d, hd, hlo⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (9 / d)
  have hM' : 9 < d * (M:ℝ) := by simpa [mul_comm] using (div_lt_iff₀ hd).mp hM
  obtain ⟨n,D,G,hn,hG,hw⟩ := nice_family M
  let B := leaves n D \ G
  have hsub : G ⊆ leaves n D := by
    intro w hg
    obtain ⟨hl, ht, he, _⟩ := hG w hg
    exact leaves_mem_of_ending n D w hl ht (Or.inr (Or.inl he))
  have hsum := Finset.sum_sdiff (f := fun w : Word => (1:ℝ)/slope w) hsub
  change (∑ w ∈ B, (1:ℝ)/slope w) + (∑ w ∈ G, (1:ℝ)/slope w) = _ at hsum
  rw [sum_leaves_weight, hw] at hsum
  have hpow : (0:ℝ) < 2^n := by positivity
  have hnonneg : 0 ≤ (M:ℝ)/(9*2^n) := by positivity
  have hweight : (∑ w ∈ B, (1:ℝ)/slope w) ≤ 1 := by linarith
  have hgap : (1:ℝ)/2^n < d * (1 - ∑ w ∈ B, (1:ℝ)/slope w) := by
    rw [show 1 - (∑ w ∈ B, (1:ℝ)/slope w) = (M:ℝ)/(9*2^n) by linarith, ← mul_div_assoc]
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<9) hpow)).mpr
    have : (1:ℝ)/2^n * (9*2^n) = 9 := by field_simp
    rwa [this]
  have hlo' : ∀ᶠ x : ℕ in atTop, d*x ≤ (population x : ℝ) := by
    simpa only [population_eq_ncard] using hlo
  refine finite_density_contradiction population B slope (fun w _ => slope_pos w) d ((1:ℝ)/2^n)
    ((9^(D+1)+1 : ℕ) : ℝ) hd population_le hlo' hweight hgap ?_
  apply Eventually.of_forall
  intro x
  have hx := population_bound (n := n) (D := D) (G := G)
    (fun w h => ⟨(hG w h).2.1, (hG w h).2.2.2⟩) x
  have hcast : (population x : ℝ) ≤ ((9^(D+1)+1 : ℕ) : ℝ) + ((x / 2^n : ℕ) : ℝ) +
      ∑ w ∈ B, (population (x / slope w) : ℝ) := by
    exact_mod_cast hx
  have hfloor : ((x / 2^n : ℕ) : ℝ) ≤ ((1:ℝ)/2^n)*x := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hpow).mpr
    exact_mod_cast Nat.div_mul_le_self x (2^n)
  linarith
