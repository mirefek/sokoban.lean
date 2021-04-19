import tactic
import .direction
import .list2d
import .boolset2d

structure sokoban :=
(available : bset2d)
(boxes : bset2d)
(storages : bset2d)
(storekeeper : ℕ × ℕ)

namespace sokoban

instance : inhabited sokoban
:= ⟨{ available := [[tt]], boxes := [], storages := [], storekeeper := (0,0) }⟩

def move (d : direction) (s : sokoban) : sokoban :=
  let sk2 := (d.shift s.storekeeper) in
  match s.available.get2d sk2 with ff := s | tt :=
  match s.boxes.get2d sk2  with ff :=
    { storekeeper := sk2, ..s}
  | tt :=
    let box2 := (d.shift sk2) in
    match !(s.available.get2d box2) || (s.boxes.get2d box2) with tt := s
    | ff :=
    {
      boxes := (s.boxes.set2d ff sk2).set2d tt box2,
      storekeeper := sk2, ..s
    }
  end end
  end

def move_up := move direction.up
def move_down := move direction.down
def move_left := move direction.left
def move_right := move direction.right

def add_newline (s : sokoban) : sokoban := {
  available := []::s.available,
  boxes := []::s.boxes,
  storages := []::s.storages,
  storekeeper := match s.storekeeper with (x,y) := (x,y+1) end
}
def add_newsquare (av box stor sk : bool) (s : sokoban) : sokoban := {
  available := list2d.add_to_line1 av s.available,
  boxes := list2d.add_to_line1 box s.boxes,
  storages := list2d.add_to_line1 stor s.storages,
  storekeeper := if sk then (0, 0) else match s.storekeeper with
    | (x,0) := (x+1,0)
    | xy := xy
  end
}

def from_string_aux : list char → option (sokoban × bool)
| [] := some (sokoban.mk [] [] [] (0,0), ff)
| (c::str) := match (from_string_aux str), c with
  | none, _ := none
  | (some (s, sk_set)), '\n' := some (add_newline s, sk_set)
  | (some (s, sk_set)), ' ' := some (add_newsquare tt ff ff ff s, sk_set)
  | (some (s, sk_set)), '#' := some (add_newsquare ff ff ff ff s, sk_set)
  | (some (s, sk_set)), '.' := some (add_newsquare tt ff tt ff s, sk_set)
  | (some (s, sk_set)), '$' := some (add_newsquare tt tt ff ff s, sk_set)
  | (some (s, sk_set)), '*' := some (add_newsquare tt tt tt ff s, sk_set)
  | (some (s, ff)), '@' := some (add_newsquare tt ff ff tt s, tt)
  | (some (s, ff)), '+' := some (add_newsquare tt ff tt tt s, tt)
  | (some _), _ := none
  end

def from_string (str : string) : sokoban :=
  match (from_string_aux str.to_list) with
  | none := default sokoban
  | some (_, ff) := default sokoban
  | some (level, tt) := level
  end

def square_to_char : bool → bool → bool → bool → char
| tt ff ff ff := ' '
| ff ff ff ff := '#'
| tt ff tt ff := '.'
| tt tt ff ff := '$'
| tt tt tt ff := '*'
| tt ff ff tt := '@'
| tt ff tt tt := '+'
| _ _ _ _ := '?'

def to_string_aux1 (str : list char) : list (bool × bool × bool × bool) → list char
| [] := str
| ((av,box,stor,sk)::t) := (square_to_char av box stor sk)::(to_string_aux1 t)

def to_string_aux2 : list2d (bool × bool × bool × bool) → list char
| [] := []
| (h::t) := to_string_aux1 ('\n'::(to_string_aux2 t)) h

instance : has_to_string sokoban := ⟨λ s,
  list.as_string (to_string_aux2
  (s.available.dfzip2d (s.boxes.dfzip2d (s.storages.dfzip2d (list2d.set2d true [] s.storekeeper)))))
⟩

instance : has_repr sokoban
:= ⟨λ s, (string.append (string.append "sokoban.from_string \"" (to_string s)) "\"")⟩

inductive solvable : sokoban -> Prop
| solved (s : sokoban) (H : s.boxes = s.storages) : solvable s
| move (d : direction) (s : sokoban) (H : solvable (s.move d)) : solvable s

def solvable.move_up := solvable.move direction.up
def solvable.move_down := solvable.move direction.down
def solvable.move_left := solvable.move direction.left
def solvable.move_right := solvable.move direction.right

meta def soko_simp_root (e : expr) : tactic unit :=
do
  soko ← tactic.eval_expr sokoban e,
  tactic.trace (to_string soko),
  let p : pexpr := ``(%%e = sokoban.mk
    %%soko.available %%soko.boxes %%soko.storages %%soko.storekeeper),
  eq ← tactic.to_expr p,
  name ← tactic.get_unused_name,
  H ← tactic.assert name eq,
  tactic.reflexivity,
  tactic.rewrite_target H,
  tactic.clear H

meta def soko_simp_expr : expr → tactic unit := assume e : expr,
soko_simp_root e <|> match e with
| expr.app e1 e2 := soko_simp_expr e1 >> soko_simp_expr e2
| _ := return ()
end

meta def soko_simp : tactic unit :=
do
  goal ← tactic.target,
  soko_simp_expr goal

meta def solve_up : tactic unit := tactic.apply `(solvable.move_up) >> soko_simp
meta def solve_down : tactic unit := tactic.apply `(solvable.move_down) >> soko_simp
meta def solve_left : tactic unit := tactic.apply `(solvable.move_left) >> soko_simp
meta def solve_right : tactic unit := tactic.apply `(solvable.move_right) >> soko_simp
meta def solve_finish : tactic unit := tactic.apply `(sokoban.solvable.solved) >> tactic.reflexivity

end sokoban

def soko_level := sokoban.from_string "
#######
#. . .#
# $$$ #
#.$@$.#
# $$$ #
#. . .#
#######
"

example : soko_level.solvable :=
begin
  sokoban.soko_simp,
  sokoban.solve_up,
  sokoban.solve_right,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_down,
  sokoban.solve_left,
  sokoban.solve_right,
  sokoban.solve_right,
  sokoban.solve_up,
  sokoban.solve_right,
  sokoban.solve_up,
  sokoban.solve_down,
  sokoban.solve_left,
  sokoban.solve_left,
  sokoban.solve_up,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_right,
  sokoban.solve_up,
  sokoban.solve_up,
  sokoban.solve_up,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_right,
  sokoban.solve_down,
  sokoban.solve_right,
  sokoban.solve_right,
  sokoban.solve_right,
  sokoban.solve_up,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_down,
  sokoban.solve_down,
  sokoban.solve_right,
  sokoban.solve_up,
  sokoban.solve_left,
  sokoban.solve_up,
  sokoban.solve_up,
  sokoban.solve_up,
  sokoban.solve_left,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_down,
  sokoban.solve_down,
  sokoban.solve_down,
  sokoban.solve_right,
  sokoban.solve_right,
  sokoban.solve_up,
  sokoban.solve_up,
  sokoban.solve_left,
  sokoban.solve_down,
  sokoban.solve_up,
  sokoban.solve_up,
  sokoban.solve_finish
end
