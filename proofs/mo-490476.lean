import OMAStatements.S_mo_490476
import Mathlib

open OMA.S_mo_490476

theorem OMA.solution : type_of% @OMA.S_mo_490476.main := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := (h Empty Unit Unit (fun e => e.elim)).1
    have hinj : Function.Injective (precomp (fun e : Empty => e.elim) : (Unit → Unit) → (Empty → Unit)) := by
      intro g1 g2 _
      funext y
      rfl
    obtain ⟨x, _⟩ := h1.mp hinj ()
    exact x.elim
  · intro X Y Z _ f
    classical
    obtain ⟨a, b, hab⟩ := exists_pair_ne Z
    constructor
    · constructor
      · intro hinj y
        by_contra hy
        push_neg at hy
        have : (fun _ : Y => a) = Function.update (fun _ : Y => a) y b := by
          apply hinj
          funext x
          simp only [precomp, Function.comp_apply]
          rw [Function.update_of_ne (hy x)]
        have h2 := congrFun this y
        simp at h2
        exact hab h2
      · intro hs g1 g2 hg
        funext y
        obtain ⟨x, rfl⟩ := hs y
        exact congrFun hg x
    · constructor
      · intro hs x1 x2 hx
        by_contra hne
        obtain ⟨g, hg⟩ := hs (fun x => if x = x1 then a else b)
        have e1 := congrFun hg x1
        have e2 := congrFun hg x2
        simp only [precomp, Function.comp_apply, if_pos rfl, if_neg (Ne.symm hne)] at e1 e2
        rw [hx] at e1
        exact hab (e1.symm.trans e2)
      · intro hinj h
        refine ⟨fun y => if hy : ∃ x, f x = y then h hy.choose else a, ?_⟩
        funext x
        simp only [precomp, Function.comp_apply]
        have hx : ∃ x', f x' = f x := ⟨x, rfl⟩
        rw [dif_pos hx]
        congr 1
        exact hinj hx.choose_spec
