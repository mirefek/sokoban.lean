import data.list.func
import .list2d

namespace list2d

open list.func

variables {α : Type} {β : Type}

def find_indexes2d {α : Type} (P : α → Prop) [decidable_pred P] (l : list2d α) : list (ℕ × ℕ)
:= list.join (l.map_with_index (λ (y:ℕ) (row:list α),
   (list.join (row.map_with_index (λ (x:ℕ) (a:α), if P a then [(x,y)] else [])))
  ))

variables [inhabited α] [inhabited β]

lemma my_add_rearrange {n n0 : ℕ} : n + 1 + n0 = n + (n0 + 1) :=
begin rw add_assoc, rw add_comm 1 n0, end

theorem my_map_with_index_core_lemma1 (f : ℕ → α → β)
  : ∀ (n n0 : ℕ) (l : list α), n < l.length →
  f (n+n0) (get n l) ∈ list.map_with_index_core f n0 l
| _ _ [] H := by cases H
| 0 n0 (h::t) H := begin apply or.inl, simp, end
| (n+1) n0 (h::t) H := begin
  apply or.inr, simp,
  rw my_add_rearrange, apply my_map_with_index_core_lemma1,
  apply nat.lt_of_succ_lt_succ H,
end
theorem my_map_with_index_lemma1 (f : ℕ → α → β) (n : ℕ)
  : ∀ (l : list α), n < l.length →
  f n (get n l) ∈ list.map_with_index f l :=
my_map_with_index_core_lemma1 f n 0

theorem my_map_with_index_core_lemma2 (f : ℕ → α → β) (b : β)
  : ∀ (n0 : ℕ) (l : list α), b ∈ list.map_with_index_core f n0 l →
  ∃ n, b = f (n+n0) (get n l)
| _ [] H := begin simp [list.map_with_index_core] at H, exact H.elim, end
| n0 (h::t) H := begin
  simp [list.map_with_index_core] at H, cases H with H0 H1,
  { existsi 0, simp, exact H0, }, {
    cases my_map_with_index_core_lemma2 (n0+1) t H1 with n H,
    existsi n+1, simp! [my_add_rearrange, H],
  }
end

theorem my_map_with_index_lemma2 (f : ℕ → α → β) (b : β)
  : ∀ (l : list α), b ∈ list.map_with_index f l →
  ∃ n, b = f n (get n l) := my_map_with_index_core_lemma2 f b 0

theorem find_indexes2d_iff (P : α → Prop) [decidable_pred P] (Hnd : ¬ P (default α))
  : ∀ (l : list2d α) (xy : ℕ × ℕ), P (l.get2d xy) ↔ xy ∈ find_indexes2d P l :=
begin
  unfold find_indexes2d, intros l xy, cases xy with x y, unfold get2d,
  generalize Erow : (λ (y:ℕ) (row:list α),
    (list.join (row.map_with_index (λ (x:ℕ) (a:α), if P a then [(x,y)] else [])))
  ) = row_f,
  split, {
    generalize Eel : (λ (x:ℕ) (a:α), if P a then [(x,y)] else []) = el_f,
    intro H, apply list.mem_join.mpr,
    existsi row_f y (get y l), split, {
      apply my_map_with_index_lemma1,
      by_contradiction C,
      have := get_eq_default_of_le y (not_lt.mp C),
      rw this at H, simp [default] at H, exact Hnd H,
    }, {
      rw ←Erow, simp, rw Eel, existsi el_f x (get x (get y l)), split,
      apply my_map_with_index_lemma1, {
        by_contradiction C,
        have := get_eq_default_of_le x (not_lt.mp C),
        rw this at H, exact Hnd H,
      },
      rw ←Eel, simp [H],
    }
  }, {
    intros H, rcases list.mem_join.mp H with ⟨l2, H1, H2⟩, clear H,
    cases my_map_with_index_lemma2 row_f l2 l H1 with y' H1,
    rw ←Erow at H1, simp at H1,
    generalize Eel : (λ (x:ℕ) (a:α), if P a then [(x,y')] else []) = el_f,
    rw Eel at H1, rw H1 at H2,
    rcases list.mem_join.mp H2 with ⟨lxy, Hmi, Hxy⟩, clear H1 H2,
    cases my_map_with_index_lemma2 el_f lxy (get y' l) Hmi with x' Hxy',
    rw ←Eel at Hxy', rw Hxy' at Hxy, clear Hxy', simp at Hxy,
    by_cases H' : (P (get x' (get y' l))),
    { simp [H'] at Hxy, cases Hxy with Hx Hy, rw [Hx,Hy], exact H', },
    { simp [H'] at Hxy, exact false.elim Hxy, },
  }
end

end list2d
