import data.fintype.basic
import data.prod

inductive direction : Type
| up
| down
| left
| right

namespace direction

def luniv := [up, down, left, right]

def opposite : direction -> direction
| up := down
| down := up
| left := right
| right := left

def transpose : direction -> direction
| up := left
| down := right
| left := up
| right := down

def shift : direction -> (ℕ × ℕ) -> (ℕ × ℕ)
| up (x, y)    := (x, y.pred)
| down (x, y)  := (x, y.succ)
| left (x, y)  := (x.pred, y)
| right (x, y) := (x.succ, y)

lemma luniv_complete {d : direction} : d ∈ luniv :=
begin unfold luniv, cases d, all_goals {simp, } end

lemma opposite_opposite {d : direction}
  : opposite (opposite d) = d :=
begin cases d, all_goals { unfold opposite, } end

theorem transpose_shift : ∀ (d : direction) (xy : ℕ×ℕ),
  d.transpose.shift xy =  (d.shift xy.swap).swap := 
begin
  intros, cases xy with x y, cases d,
  all_goals { refl, },
end

theorem opposite_shift : ∀ (d : direction) (xy : ℕ×ℕ),
  d.shift xy = xy ∨ d.opposite.shift (d.shift xy) = xy
| up (x, 0) := by simp! [opposite, shift]
| up (x, y+1) := by simp! [opposite, shift]
| down (x, y) := by simp! [opposite, shift]
| left (0, y) := by simp! [opposite, shift]
| left (x+1, y) := by simp! [opposite, shift]
| right (x, y) := by simp! [opposite, shift]

end direction
