import tactic
import data.list.func
variables {α : Type} {β : Type}
variables [inhabited α] [inhabited β]

def forall2_inh_dec (P : α → β → Prop) [Hdec : Π a b, decidable (P a b)]
: Π (l1 : list α) (l2 : list β),
  decidable (∀ n, P (list.func.get n l1) (list.func.get n l2))
| [] [] := begin
  apply decidable_of_decidable_of_iff (Hdec (default α) (default β)),
  split,
  { intros H n, simp, exact H, },
  { intros H, simp at H, exact H, },
end
| (h1::t1) [] := begin
  haveI := forall2_inh_dec t1 [],
  apply decidable_of_iff (P h1 (default β) ∧ (∀ n, P (list.func.get n t1) (list.func.get n []))),
  split, {
    intros H n, cases n, simp, exact H.left,
    simp, have H := H.right n, simp at H, exact H,
  }, {
    intros H, split, have H := (H 0), simp at H, exact H,
    intro n, have H := H n.succ, simp, simp at H, exact H,
  }
end
| [] (h2::t2) := begin
  haveI := forall2_inh_dec [] t2,
  apply decidable_of_iff (P (default α) h2 ∧ (∀ n, P (list.func.get n []) (list.func.get n t2))),
  split, {
    intros H n, cases n, simp, exact H.left,
    simp, have H := H.right n, simp at H, exact H,
  }, {
    intros H, split, have H := (H 0), simp at H, exact H,
    intro n, have H := H n.succ, simp, simp at H, exact H,
  }
end
| (h1::t1) (h2::t2) := begin
  haveI := forall2_inh_dec t1 t2,
  apply decidable_of_iff (P h1 h2 ∧ (∀ n, P (list.func.get n t1) (list.func.get n t2))),
  split, {
    intros H n, cases n, simp, exact H.left,
    simp, have H := H.right n, exact H,
  }, {
    intros H, split, have H := (H 0), exact H,
    intro n, have H := H n.succ, exact H,
  }
end

instance list.equiv_decidable [decidable_eq α] : @decidable_rel (list α) list.func.equiv
:= forall2_inh_dec eq

#eval to_bool (list.func.equiv [1,2,3] [1,2,3,0])
-- tt

--#reduce to_bool (list.func.equiv [1,2,3] [1,2,3,0])

#reduce to_bool (4 < 10)

example : (list.func.equiv [1,2,3] [1,2,3,0]) := begin
  dec_trivial
end
-- fails
