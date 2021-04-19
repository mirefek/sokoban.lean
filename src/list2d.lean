import tactic
import data.list.func

universe u

def list2d (α : Type u) := list (list α)

namespace list2d

open list.func

variables {α : Type} {β : Type} {γ : Type} {δ : Type}
variables [inhabited α] [inhabited β]

def get2d (xy : ℕ × ℕ) (l : list2d α) : α
  := let (x,y) := xy in get x (get y l)
def set2d (a : α) (l : list2d α) (xy : ℕ × ℕ) : list2d α
  := let (x,y) := xy in set (set a (get y l) x) l y
def map2d (f : γ → δ) : list2d γ → list2d δ
  := list.map (list.map f)
def fold2d (f : γ → δ → δ) : δ → list2d γ → δ
  := list.foldr (function.swap (list.foldr f))
def pointwise2d (f : α → β → γ) : list2d α → list2d β → list2d γ
  := pointwise (pointwise f)
def dfzip2d : list2d α → list2d β → list2d (α × β)
  := pointwise2d prod.mk

def equiv (l1 l2 : list2d α)
  := ∀ (xy : ℕ × ℕ), l1.get2d xy = l2.get2d xy

def add_to_line1 (a : α) : list2d α -> list2d α
| [] := [[a]]
| (h::t) := (a::h)::t

@[simp] lemma get2d_nil : ∀ xy : ℕ×ℕ, get2d xy ([] : list2d α) = default α
| (x,y) := by simp [get2d, default]

def transpose : list2d α → list2d α := (list.foldr (pointwise list.cons)) []

instance [has_repr α] : has_repr (list2d α) := ⟨λ l, list.repr (l : list (list α))⟩

private lemma g_get_pointwise {δ : Type} [inhabited γ] {f : α → β → γ} (g : γ -> δ)
  (h1 : g (f (default α) (default β)) = g (default γ)) :
  ∀ (k : nat) (as : list α) (bs : list β),
  g (get k (pointwise f as bs)) = g (f (get k as) (get k bs))
| k [] [] := by simp only [h1, get_nil, list.func.pointwise, list.func.get]
| 0 [] (b::bs) :=
  by simp only [get_pointwise, get_nil,
      list.func.pointwise, list.func.get, nat.nat_zero_eq_zero, list.map]
| (k+1) [] (b::bs) :=
  by { have : g (get k (list.map (f $ default α) bs)) = g (f (default α) (get k bs)),
       { simpa [nil_pointwise, get_nil] using (g_get_pointwise k [] bs) },
       simpa [list.func.get, get_nil, pointwise, list.map] }
| 0 (a::as) [] :=
  by simp only [g_get_pointwise, get_nil,
     list.func.pointwise, list.func.get, nat.nat_zero_eq_zero, list.map]
| (k+1) (a::as) [] :=
  by simpa [list.func.get, get_nil, pointwise, list.map, pointwise_nil, get_nil]
     using g_get_pointwise k as []
| 0 (a::as) (b::bs) := by simp only [list.func.pointwise, list.func.get]
| (k+1) (a::as) (b::bs) :=
  by simp only [list.func.pointwise, list.func.get, g_get_pointwise k]

@[simp] theorem get2d_transpose : ∀ (xy : ℕ × ℕ) (l : list2d α),
  get2d xy (transpose l) = get2d (prod.swap xy) l :=
begin
  intros, cases xy with x y, simp, revert x, induction l, {
    intros, unfold transpose, unfold get2d,
    simp [default],
  }, {
    intros, unfold get2d, unfold transpose,
    simp [list.foldr], rewrite g_get_pointwise (get x),
    cases x, refl, apply l_ih,
    simp [default], cases x, refl, simp,
  }
end

@[simp] theorem map_pointwise {δ : Type}
  (f : α → β → γ) (g : γ → δ) : ∀ (l1 : list α) (l2 : list β),
  list.map g (list.func.pointwise f l1 l2)
  = list.func.pointwise (λ a b, g (f a b)) l1 l2
| [] [] := by simp
| (a::as) [] := by simp 
| [] (b::bs) := by simp
| (a::as) (b::bs) := by simp [(map_pointwise as bs)]

@[simp] theorem map_map_circ {δ2 : Type} (f : δ → δ2) (g : γ → δ) : (list.map f) ∘ (list.map g) = list.map (f ∘ g) :=
begin apply funext, simp end

theorem nil_pointwise_curry {f : α → β → γ} : pointwise f list.nil = list.map (f (default α)) := begin apply funext, intros, apply nil_pointwise end

theorem map_pointwise2d
  (f : α → β → γ) (g : γ → δ) : ∀ (l1 : list2d α) (l2 : list2d β),
  map2d g (pointwise2d f l1 l2)
  = pointwise2d (λ a b, g (f a b)) l1 l2 :=
begin
  intros, unfold map2d, unfold pointwise2d, simp
end

theorem pointwise_dfzip2d
  (f : α → β → γ) : ∀ (l1 : list2d α) (l2 : list2d β),
  pointwise2d f l1 l2 =
(pointwise2d prod.mk l1 l2).map2d (λ ab, match ab with (a,b) := f a b end) :=
by simp [map_pointwise2d]

theorem get2d_pointwise [inhabited γ] {f : α → β → γ}
  (H : f (default α) (default β) = default γ) :
  ∀ (xy : ℕ×ℕ) (as : list2d α) (bs : list2d β),
  get2d xy (pointwise2d f as bs) = f (get2d xy as) (get2d xy bs) :=
begin
  intros, cases xy with x y, unfold get2d, unfold pointwise2d,
  repeat { rw list.func.get_pointwise, }, exact H,
  simp! [default],
end

theorem get2d_set2d {a : α} {xy : ℕ×ℕ} {l : list2d α} : (l.set2d a xy).get2d xy = a :=
begin
  cases xy with x y, unfold get2d, unfold set2d, simp!,
end
theorem get2d_set2d_eq_of_ne {a : α} {xy1 xy2 : ℕ×ℕ} {l : list2d α}
  : xy1 ≠ xy2 → (l.set2d a xy2).get2d xy1 = (l.get2d xy1) :=
begin
  cases xy1 with x1 y1,
  cases xy2 with x2 y2,
  unfold get2d, unfold set2d,
  intro H,
  by_cases Hy : y1 = y2, {
    rw Hy, rw Hy at H, rw get_set,
    by_cases Hx : x1 = x2,
    { exfalso, rw Hx at H, exact H rfl, },
    { exact get_set_eq_of_ne x2 x1 Hx, },
  }, {
    apply congr_arg, exact get_set_eq_of_ne y2 y1 Hy,
  },
end

end list2d
