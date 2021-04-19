import data.list.func
import .list2d
import .boolset2d

variables {α : Type} {β : Type}
variables [inhabited α] [inhabited β]

def forall1_inh_bool (P : α → bool) : list α → bool
| [] := P (default α)
| (h::t) := (P h) && (forall1_inh_bool t)
def forall2_inh_bool (P : α → β → bool) : list α → list β → bool
| [] l2 := forall1_inh_bool (P (default α)) l2
| (h::t) l2 := (P h l2.head) && (forall2_inh_bool t l2.tail)

lemma forall1_inh_bool.correct (P : α → Prop) [Hdec : Π a, decidable (P a)]
: ∀ l1 : list α,
forall1_inh_bool (λ a, to_bool (P a)) l1 ↔ ∀ n, P (list.func.get n l1)
| [] := by simp [forall1_inh_bool]
| (h::t) := begin
  simp [forall1_inh_bool, forall1_inh_bool.correct],
  split, assume H n, cases n, exact H.1, exact H.2 n,
  assume H, split, exact H 0, assume n, exact H n.succ,
end

lemma forall2_inh_bool.correct (P : α → β → Prop) [Hdec : Π a b, decidable (P a b)]
: ∀ l1 : list α, ∀ l2 : list β,
forall2_inh_bool (λ a b, to_bool (P a b)) l1 l2
↔ ∀ n, P (list.func.get n l1) (list.func.get n l2)
| [] l2 := by simp [forall2_inh_bool, forall1_inh_bool.correct]
| (h::t) l2 := begin
  simp [forall2_inh_bool, forall2_inh_bool.correct],
  split, {
    assume H n, cases n, 
    { cases l2, exact H.1, exact H.1 },
    { cases l2, simp, simp at H, exact H.2 n, simp [list.tail] at H, exact H.2 n, },
  }, {
    assume H, split,
    { cases l2, exact H 0, exact H 0, },
    { assume n, cases l2, simp, simp at H, exact H n.succ, simp [list.tail], exact H n.succ, },
  }
end

def forall2_inh_dec (P : α → β → Prop) [Hdec : Π a b, decidable (P a b)]
(l1 : list α) (l2 : list β)
: decidable (∀ n, P (list.func.get n l1) (list.func.get n l2))
:=
if C : forall2_inh_bool (λ a b, to_bool (P a b)) l1 l2 = tt then
  is_true ((forall2_inh_bool.correct P l1 l2).mp C)
else is_false (mt (forall2_inh_bool.correct P l1 l2).mpr C)

instance equiv_decidable [decidable_eq α] : @decidable_rel (list α) list.func.equiv
:= forall2_inh_dec eq

def forall2d2_inh_dec (P : α → β → Prop) [Hdec : Π a b, decidable (P a b)]
(l1 : list2d α) (l2 : list2d β) :
  decidable (∀ xy, P (list2d.get2d xy l1) (list2d.get2d xy l2))
:= begin
  let P2 := λ (as : list α) (bs : list β), ∀ x, P (list.func.get x as) (list.func.get x bs),
  haveI : ∀ a b, decidable (P2 a b) := forall2_inh_dec P,
  haveI := forall2_inh_dec P2 l1 l2,
  apply decidable_of_iff (∀ y, P2 (list.func.get y l1) (list.func.get y l2)),
  split,
  { intros H xy, cases xy with x y, exact H y x, },
  { intros H y x, exact H (x,y), },
end

instance list.equiv_decidable [decidable_eq α] : @decidable_rel (list α) list.func.equiv
:= forall2_inh_dec eq
instance list2d.equiv_decidable [decidable_eq α] : @decidable_rel (list2d α) list2d.equiv
:= forall2d2_inh_dec eq
instance : decidable_rel bset1d.subset
:= forall2_inh_dec (λ a b, a = tt → b = tt)
instance : decidable_rel bset2d.subset
:= forall2d2_inh_dec (λ a b, a = tt → b = tt)
instance : decidable_rel bset2d.disjoint
:= forall2d2_inh_dec (λ a b, a = tt → b = tt → false)
