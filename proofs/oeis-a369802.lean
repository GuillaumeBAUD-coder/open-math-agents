import OMAStatements.S_oeis_a369802

/-!
At depth h, the nodes of a complete binary tree are inserted in numerical
order into the gaps of the in-order traversal of the preceding levels.
The jth such insertion puts the largest label before exactly 2^h-1-j
old labels. This counts the new inversions directly.
-/

namespace EytzingerInversions

open OMA.S_oeis_a369802

private def tree : ℕ → ℕ → List ℕ
  | 0, _ => []
  | h + 1, k => tree h (2*k) ++ k :: tree h (2*k+1)

private theorem tree_length (h k : ℕ) : (tree h k).length + 1 = 2^h := by
  induction h generalizing k with
  | zero => simp [tree]
  | succ h ih =>
    simp only [tree, List.length_append, List.length_cons, pow_succ]
    have hl := ih (2*k)
    have hr := ih (2*k+1)
    omega

private theorem tree_lower (h k x : ℕ) (hx : x ∈ tree h k) : k ≤ x := by
  induction h generalizing k with
  | zero => simp [tree] at hx
  | succ h ih =>
    simp only [tree, List.mem_append, List.mem_cons] at hx
    rcases hx with hl | rfl | hr
    · have := ih _ hl; omega
    · exact le_rfl
    · have := ih _ hr; omega

private theorem tree_upper (h k x : ℕ) (hx : x ∈ tree (h+1) k) :
    x < 2^h * (k+1) := by
  induction h generalizing k with
  | zero =>
    have h : x = k := by simpa [tree] using hx
    subst x
    simp
  | succ h ih =>
    change x ∈ tree (h+1) (2*k) ++ k :: tree (h+1) (2*k+1) at hx
    simp only [List.mem_append, List.mem_cons] at hx
    rw [pow_succ]
    have hp : 0 < 2^h := by positivity
    rcases hx with hl | he | hr
    · have := ih _ hl; nlinarith
    · subst x
      nlinarith [Nat.mul_le_mul_right (k+1) (show 1 ≤ 2^h by omega)]
    · have := ih _ hr; nlinarith

private theorem root_upper (h x : ℕ) (hx : x ∈ tree h 1) : x < 2^h := by
  cases h with
  | zero => simp [tree] at hx
  | succ h => simpa [pow_succ] using tree_upper h 1 x hx

private theorem traversal (h n k : ℕ) (hk : 0 < k) (bound : n < 2^h * k) :
    eytzingerOrder n k = (tree h k).filter (fun x => decide (x ≤ n)) := by
  by_cases hkn : k ≤ n
  · induction h generalizing k with
    | zero => simp at bound; omega
    | succ h ih =>
      have hl : n < 2^h * (2*k) := by simpa [pow_succ, Nat.mul_assoc] using bound
      have hr : n < 2^h * (2*k+1) := by nlinarith [show 0 < 2^h by positivity]
      rw [eytzingerOrder, dif_pos ⟨hk,hkn⟩, tree, List.filter_append]
      have child (u : ℕ) (hu : 0 < u) (hb : n < 2^h*u) :
          eytzingerOrder n u = (tree h u).filter (fun x => decide (x ≤ n)) := by
        by_cases hu' : u ≤ n
        · exact ih u hu hb hu'
        · rw [eytzingerOrder, dif_neg (by omega)]
          symm
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have := tree_lower h u x hx
          simp [show ¬ x ≤ n by omega]
      simp [hkn, child (2*k) (by omega) hl, child (2*k+1) (by omega) hr, List.append_assoc]
  · rw [eytzingerOrder, dif_neg (by omega)]
    symm
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have := tree_lower h k x hx
    simp [show ¬ x ≤ n by omega]

/-- Put consecutively labelled leaves in the gaps of an in-order list. -/
private def sprout : List ℕ → ℕ → List ℕ
  | [], s => [s]
  | x :: xs, s => s :: x :: sprout xs (s+1)

private theorem sprout_append (l r : List ℕ) (x s : ℕ) :
    sprout (l ++ x :: r) s = sprout l s ++ x :: sprout r (s + l.length + 1) := by
  induction l generalizing s with
  | nil => simp [sprout]
  | cons y ys ih => simp [sprout, ih, Nat.add_comm, Nat.add_left_comm]

private theorem tree_sprout (h k : ℕ) :
    tree (h+1) k = sprout (tree h k) (2^h*k) := by
  induction h generalizing k with
  | zero => simp [tree, sprout]
  | succ h ih =>
    change tree (h+1) (2*k) ++ k :: tree (h+1) (2*k+1) =
      sprout (tree h (2*k) ++ k :: tree h (2*k+1)) (2^(h+1)*k)
    rw [ih, ih, sprout_append]
    have hl := tree_length h (2*k)
    rw [show 2^h*(2*k) = 2^(h+1)*k by ring,
      show 2^(h+1)*k + (tree h (2*k)).length + 1 = 2^h*(2*k+1) by
        rw [pow_succ]; nlinarith]

private theorem below (l : List ℕ) (s b : ℕ) (hs : b ≤ s) (hl : ∀ x ∈ l, x < b) :
    (sprout l s).filter (fun x => decide (x < b)) = l := by
  induction l generalizing s with
  | nil => simp [sprout, Nat.not_lt.mpr hs]
  | cons x xs ih =>
    have hx := hl x (by simp)
    have hxs (y) (hy : y ∈ xs) := hl y (by simp [hy])
    simp [sprout, Nat.not_lt.mpr hs, hx, ih (s+1) (by omega) hxs]

private theorem at_first (l : List ℕ) (s : ℕ) (hl : ∀ x ∈ l, x < s) :
    (sprout l s).filter (fun x => decide (x < s+1)) = s :: l := by
  cases l with
  | nil => simp [sprout]
  | cons x xs =>
    have hx := hl x (by simp)
    have hxs (y) (hy : y ∈ xs) : y < s+1 := by
      have := hl y (by simp [hy])
      omega
    rw [sprout, List.filter_cons_of_pos (by simp),
      List.filter_cons_of_pos (by simp [show x < s+1 by omega]), below xs (s+1) (s+1) le_rfl hxs]

/-- Revealing the jth leaf inserts one label, with exactly length(l)-j old
labels on its right. -/
private theorem split_leaf (l : List ℕ) (s j : ℕ) (hj : j ≤ l.length)
    (hl : ∀ x ∈ l, x < s) :
    ∃ pre post : List ℕ,
      (sprout l s).filter (fun x => decide (x < s+j)) = pre ++ post ∧
      (sprout l s).filter (fun x => decide (x < s+j+1)) = pre ++ (s+j) :: post ∧
      post.length = l.length - j := by
  induction l generalizing s j with
  | nil =>
    have : j = 0 := by simpa using hj
    subst j
    exact ⟨[], [], by simp [sprout], by simp [sprout], by simp⟩
  | cons x xs ih =>
    cases j with
    | zero =>
      exact ⟨[], x :: xs, by simpa using below (x::xs) s s le_rfl hl,
        by simpa using at_first (x::xs) s hl, by simp⟩
    | succ j =>
      have hx := hl x (by simp)
      have hxs (y) (hy : y ∈ xs) : y < s+1 := by
        have := hl y (by simp [hy]); omega
      obtain ⟨pre, post, old, new, sz⟩ := ih (s+1) j (by simpa using hj) hxs
      refine ⟨s :: x :: pre, post, ?_, ?_, by simpa using sz⟩
      · rw [show s + (j+1) = s+1+j by omega]
        simp [sprout, show s < s+1+j by omega, show x < s+1+j by omega, old]
      · rw [show s + (j+1) = s+1+j by omega]
        rw [sprout, List.filter_cons_of_pos (by exact decide_eq_true (by omega)),
          List.filter_cons_of_pos (by exact decide_eq_true (by omega)), new]
        rfl

private def inversions (l : List ℕ) : ℕ :=
  (l.tails.map fun t => match t with
    | [] => 0
    | j :: rest => (rest.filter (fun i => j > i)).length).sum

private theorem inv_cons (x : ℕ) (l : List ℕ) :
    inversions (x::l) = (l.filter (fun i => x > i)).length + inversions l := by
  simp [inversions]

private theorem insert_largest (pre post : List ℕ) (v : ℕ)
    (hv : ∀ x ∈ pre ++ post, x < v) :
    inversions (pre ++ v :: post) = inversions (pre ++ post) + post.length := by
  induction pre with
  | nil =>
    have hp : post.filter (fun i => v > i) = post :=
      List.filter_eq_self.mpr (by simpa using hv)
    simp [inv_cons, hp, Nat.add_comm]
  | cons x xs ih =>
    have hx := hv x (by simp)
    have hxs (y) (hy : y ∈ xs ++ post) := hv y (by simp [hy])
    simp only [List.cons_append, inv_cons, List.filter_append]
    simp [show ¬ v < x by omega, ih hxs, Nat.add_assoc]

private theorem increment (h j : ℕ) (hj : j < 2^h) :
    a369802 (2^h+j) = a369802 (2^h+j-1) + (2^h-1-j) := by
  let s := 2^h
  let l := tree h 1
  have hs : 0 < s := by dsimp [s]; positivity
  have len : l.length + 1 = s := tree_length h 1
  have cap (n) (hn : n < 2*s) :
      eytzingerOrder n 1 = (sprout l s).filter (fun x => decide (x ≤ n)) := by
    rw [traversal (h+1) n 1 (by decide) (by simpa [s, pow_succ, mul_comm] using hn),
      tree_sprout, Nat.mul_one]
  have hjs : j < s := hj
  obtain ⟨pre, post, old, new, sz⟩ :=
    split_leaf l s j (by omega) (root_upper h)
  have old_test : (fun x : ℕ => decide (x ≤ s+j-1)) = (fun x => decide (x < s+j)) := by
    funext x
    simp only [show x ≤ s+j-1 ↔ x < s+j by omega]
  have new_test : (fun x : ℕ => decide (x ≤ s+j)) = (fun x => decide (x < s+j+1)) := by
    funext x; simp
  change inversions (eytzingerOrder (s+j) 1) = inversions (eytzingerOrder (s+j-1) 1) + (s-1-j)
  rw [cap (s+j) (by omega), cap (s+j-1) (by omega), new_test, old_test, new, old]
  have hv (x) (hx : x ∈ pre ++ post) : x < s+j := by
    rw [← old] at hx
    simpa using (List.mem_filter.mp hx).2
  rw [insert_largest pre post (s+j) hv, sz]
  omega

private theorem stage_power (h : ℕ) : a261693 (2^h) = 2*2^h-1 := by
  have positive : 0 < 2^h := by positivity
  generalize he : 2^h = s
  cases s with
  | zero => omega
  | succ s => rw [a261693, if_pos ⟨h, he.symm⟩]

private theorem stage (h j : ℕ) (hj : j < 2^h) :
    a261693 (2^h+j) = 2*(2^h-1-j)+1 := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, Nat.sub_zero, stage_power]
    have : 0 < 2^h := by positivity
    omega
  | succ j ih =>
    have no_power : ¬ ∃ b : ℕ, 2^h+j+1 = 2^b := by
      rintro ⟨b, hb⟩
      by_cases bh : b ≤ h
      · have := Nat.pow_le_pow_right (by decide : 0 < 2) bh
        omega
      · have := Nat.pow_le_pow_right (by decide : 0 < 2) (show h+1 ≤ b by omega)
        rw [pow_succ] at this
        omega
    rw [show 2^h+(j+1) = 2^h+j+1 by omega, a261693, if_neg no_power, ih (by omega)]
    omega

private theorem total_succ (n : ℕ) : a261692 (n+1) = a261692 n + a261693 (n+1) := by
  unfold a261692
  rw [Finset.sum_Icc_succ_top (by omega)]

private theorem total (n : ℕ) : 2 * a369802 n + n = a261692 n := by
  induction n with
  | zero => simp [a369802, eytzingerOrder, a261692]
  | succ n ih =>
    let h := Nat.log 2 (n+1)
    let j := n+1-2^h
    have lower : 2^h ≤ n+1 := Nat.pow_log_le_self 2 (by omega)
    have upper : n+1 < 2^h*2 := by
      simpa [h, pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n+1)
    have hj : j < 2^h := by dsimp [j]; omega
    have eqn : 2^h+j = n+1 := by dsimp [j]; omega
    have hi := increment h j hj
    have hs := stage h j hj
    rw [eqn, Nat.add_sub_cancel] at hi
    rw [eqn] at hs
    rw [total_succ, ← ih, hi, hs]
    omega

theorem result : type_of% @OMA.S_oeis_a369802.main := by
  intro n
  have h := total n
  exact ⟨h, by omega⟩

end EytzingerInversions

theorem OMA.solution : type_of% @OMA.S_oeis_a369802.main := EytzingerInversions.result
