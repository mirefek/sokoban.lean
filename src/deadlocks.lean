import tactic
import .boolset2d
import .sokostate
import .boxint
import .sokolevel

def boxint.generate_from_list (avail : bset2d) (boxes blocks : list (ℕ × ℕ)) (sk : ℕ × ℕ) : boxint
:=
let boxes2d := (bset2d.from_indexes boxes) in
let blocks2d := (bset2d.from_indexes blocks) in
let subboxes := boxes2d ∩ avail in
let supboxes := (avail \ blocks2d) ∪ subboxes in
boxint.generate avail subboxes supboxes sk

def list.pall {α : Type} (P : α → Prop) : list α → Prop
| [] := true
| (h::t) := P h ∧ list.pall t
def list.pall_iff {α : Type} {P : α → Prop} {l : list α}
: list.pall P l ↔ (∀ a : α, a ∈ l → P a)
:=
begin
  induction l with h t IH, {
    split,
    { intros H a Hin, exfalso,
      exact list.not_mem_nil a Hin, },
    { intro H, trivial, }
  }, {
    split, {
      intros H a Hin,
      cases H with Hh Ht,
      cases Hin,
      rw Hin, exact Hh,
      exact IH.mp Ht a Hin,
    }, {
      intro H, split,
      { apply H, simp, },
      { apply IH.mpr,
        intros a Hin,
        apply H, right, exact Hin,
      }
    }
  }
end
lemma list.pall_in {α : Type} (l : list α)
: l.pall (λ a, a ∈ l) := list.pall_iff.mpr (λ a H, H)

namespace deadlocks

theorem boxint.generate_from_list_valid {avail : bset2d} {boxes blocks : list (ℕ × ℕ)} {sk : ℕ × ℕ}
: (boxint.generate_from_list avail boxes blocks sk).valid avail
:=
begin
  apply boxint.generate_valid, {
    exact bset2d.union_supset_right,
  }, {
    apply bset2d.union_subset,
    exact bset2d.sdiff_subset,
    exact bset2d.inter_subset_right,
  }
end

def deadlock (avail : bset2d) (goal : boxes_only) (as : boxint) : Prop
:= ∀ s1 s2 : sokostate, s1 ∈ as → s2 ∈ goal → s2.reachable avail s1 → false

lemma new_deadlocks {avail : bset2d} {goal : boxes_only} {new_dls : list boxint}
: (∀ as : boxint, as ∈ new_dls →
  as.valid avail ∧ as.disjoint goal ∧
  (∀ as2 : boxint, as2 ∈ as.next_states avail →
  ∃ dl : boxint, as2.subset_g dl goal ∧ (dl ∈ new_dls ∨ deadlock avail goal dl))
) → (∀ as : boxint, as ∈ new_dls → deadlock avail goal as)
:=
begin
  intro H,
  intros as Has_in s1 sg Hs1 Hsg Hr,
  revert as,
  induction Hr with s1 d Hr IH,
  { 
    assume as Has_in Hs,
    exact boxint.disjoint_correct as goal sg (H as Has_in).2.1 Hs Hsg,
  },
  {
    assume as Has_in Hs1,
    rcases H as Has_in with ⟨Hval, Hdisj, H⟩,
    cases boxint.next_of_real_move avail as Hval s1 d Hs1 with H1 H2,
    { exact IH as Has_in H1, }, -- no change in abstract state
    {
      rcases H2 with ⟨as2, Has2_next, Hin_as2⟩,
      rcases H as2 Has2_next with ⟨dl, Hdl_sup, Hdl⟩,
      let s2 := sokostate.move avail d s1,
      have : s2 ∈ dl
      := boxint.subset_g_correct Hdl_sup s2 sg Hin_as2 Hsg Hr,
      cases Hdl with Hdl_new Hdl_old,
      {
        clear H,
        exact IH dl Hdl_new this,
      },
      { apply Hdl_old s2 sg this Hsg Hr, }
    },
  }
end

lemma new_deadlock {avail : bset2d} {goal : boxes_only} {new_dl : boxint}
: (
  new_dl.valid avail ∧ new_dl.disjoint goal ∧
  (∀ as2 : boxint, as2 ∈ new_dl.next_states avail →
  ∃ dl : boxint, as2.subset_g dl goal ∧ deadlock avail goal dl)
) → deadlock avail goal new_dl
:=
begin
  rintros ⟨Hval, Hdisj, H⟩,
  have : (∀ as, as ∈ [new_dl] → deadlock avail goal as), {
    apply new_deadlocks,
    refine list.pall_iff.mp ⟨_, trivial⟩,
      refine ⟨Hval, Hdisj, _⟩,
      intros as2 Has2,
      rcases H as2 Has2 with ⟨dl, Hsub, Hdl⟩,
      existsi dl,
      split, exact Hsub,
      right, exact Hdl,
  },
  exact (list.pall_iff.mpr this).1,
end

--   _             _   _          
--  | |_ __ _  ___| |_(_) ___ ___ 
--  | __/ _` |/ __| __| |/ __/ __|
--  | || (_| | (__| |_| | (__\__ \
--   \__\__,_|\___|\__|_|\___|___/
--                                

meta def and_placeholders : ℕ → pexpr
| 0 := ``(trivial)
| (n+1) := ``(and.intro %%(pexpr.mk_placeholder) %%(and_placeholders n))

meta def analyze_deadlock : tactic unit
:=
do
  tactic.refine ``(and.intro boxint.generate_from_list_valid
    (and.intro dec_trivial (list.pall_iff.mp _))),
  `(list.pall %%_ %%steps_list) ← tactic.target,
  num_steps ← tactic.eval_expr nat `(@list.length boxint %%steps_list),
  tactic.refine (and_placeholders num_steps),
  return ()

end deadlocks

meta def get_deadlock_of_step (t : expr) : tactic (expr × bool)
:=
(do
  `(deadlocks.deadlock %%e0 %%e1 %%e) ← tactic.whnf t reducible,
  return (e, ff)
) <|> 
(do
  `(%%e ∈ %%e0) ← return t,
  return (e, tt)
)

meta def tactic.deadlocked_step (e : expr) : tactic unit :=
do
  t ← tactic.infer_type e,
  (dl, is_rep) ← get_deadlock_of_step t,
  tactic.refine ``(exists.intro %%dl (and.intro dec_trivial _)),
  if is_rep then tactic.left >> tactic.exact e
  else tactic.try tactic.right >> tactic.exact e

meta def tactic.interactive.deadlocked_step (q : interactive.parse interactive.types.texpr) : tactic unit
:= tactic.i_to_expr q >>= tactic.deadlocked_step
