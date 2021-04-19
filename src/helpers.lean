import data.list
import data.list.func

universe u

theorem get_succ {α : Type u} [inhabited α]
  : ∀ (l : list α) (n : ℕ),
  list.func.get n.succ l = list.func.get n l.tail :=
begin intros, cases l, simp, simp, end

theorem get_0_head {α : Type u} [inhabited α] (l : list α)
  : list.func.get 0 l = list.head l := 
begin cases l, simp, simp, end

lemma list.sum_tl_hd {l : list ℕ} : l.sum = l.tail.sum + l.head :=
begin
  cases l with h t, refl, simp, apply add_comm,
end

lemma list.sum_update (x : ℕ) : ∀ (l : list ℕ) (n : ℕ),
∃ c, l.sum = c + (list.func.get n l)
∧ (list.func.set x l n).sum = c + x
| l 0 := begin
  existsi l.tail.sum,
  split,
  { rw get_0_head, exact list.sum_tl_hd, },
  {
    have : ∀ y, y + x = y + (list.func.set x l 0).head, by simp [←get_0_head],
    rw this,
    have : l.tail = (list.func.set x l 0).tail,
    { cases l, simp, simp, },
    rw this,
    exact list.sum_tl_hd,
  }
end
| [] (n+1) := begin
  rcases list.sum_update [] n with ⟨c, IH1, IH2⟩,
  existsi c, split, {
    have : list.func.get (n + 1) list.nil = list.func.get n list.nil,
    rw [list.func.get_nil, list.func.get_nil],
    rw this, exact IH1,
  }, {
    simp [default, IH2],
  }
end
| (h::t) (n+1) := begin
  rcases list.sum_update t n with ⟨c, IH1, IH2⟩,
  existsi h+c, simp, split, {
    rw IH1, exact (add_assoc _ _ _).symm,
  }, {
    rw IH2, exact (add_assoc _ _ _).symm,
  }
end

lemma list.set_map {α β : Type} [inhabited α] [inhabited β]
(a : α) (f : α → β) (Hdf : default β = f (default α)) : ∀ (l : list α) (n : ℕ),
list.func.set (f a) (list.map f l) n = list.map f (list.func.set a l n)
| [] 0 := by simp
| (h::t) 0 := by simp
| [] (n+1) := begin
  simp, split, exact Hdf,
  exact list.set_map [] n,
end
| (h::t) (n+1) := begin
  simp, exact list.set_map t n,
end

lemma list.sum_map_update {α : Type} [inhabited α]
(f : α → ℕ) (Hdf : f (default α) = 0) (a : α) (l : list α) (n : ℕ)
: ∃ c, (l.map f).sum = c + f (list.func.get n l)
∧ ((list.func.set a l n).map f).sum = c + (f a)
:=
begin
  rcases list.sum_update (f a) (list.map f l) n
  with ⟨c, H1, H2⟩, existsi c, split,
  { rw H1, rw list.func.get_map', exact Hdf, },
  { rw ←H2, rw list.set_map, exact Hdf.symm, },
end
