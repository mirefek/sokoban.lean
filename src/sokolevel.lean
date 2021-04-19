import tactic
import .direction
import .boolset2d
import .listdec
import .sokostate

structure sokolevel :=
(avail : bset2d)
(ini : sokostate)
(goal : boxes_only)

instance : inhabited sokolevel
:= ⟨{ avail := [[tt]], ini := {boxes := [], storekeeper := (0,0)}, goal := ⟨[]⟩ }⟩

namespace sokolevel

def valid (level : sokolevel) := level.ini.valid level.avail
instance {level : sokolevel} : decidable level.valid
  := sokostate.valid.decidable

lemma default.valid : (default sokolevel).valid := dec_trivial

def move (level : sokolevel) (d : direction) : sokolevel
:= {ini := (level.ini.move level.avail d) ..level}

def solvable (level : sokolevel) :=
  exists goal_state : sokostate, goal_state ∈ level.goal ∧
    goal_state.reachable level.avail level.ini

lemma solvable.triv (level : sokolevel)
: level.ini ∈ level.goal → level.solvable
:= λ Hin, ⟨level.ini, ⟨Hin, sokostate.reachable.triv⟩⟩

lemma solvable.move (d : direction) (level : sokolevel)
: (level.move d).solvable → level.solvable
:= λ Hsol, exists.elim Hsol (λ goal Hsol,
  ⟨goal, ⟨Hsol.1, sokostate.reachable.move d Hsol.2⟩⟩ )

--   _                            _   
--  (_)_ __ ___  _ __   ___  _ __| |_ 
--  | | '_ ` _ \| '_ \ / _ \| '__| __|
--  | | | | | | | |_) | (_) | |  | |_ 
--  |_|_| |_| |_| .__/ \___/|_|   \__|
--              |_|                   

def add_newline (s : sokolevel) : sokolevel := {
  avail := []::s.avail,
  ini := {
    boxes := []::s.ini.boxes,
    storekeeper := match s.ini.storekeeper with (x,y) := (x,y+1) end
  },
  goal := { boxes := []::s.goal.boxes },
}
def add_newsquare (av box stor sk : bool) (s : sokolevel) : sokolevel := {
  avail := list2d.add_to_line1 av s.avail,
  ini := {
    boxes := list2d.add_to_line1 box s.ini.boxes,
    storekeeper := if sk then (0, 0) else match s.ini.storekeeper with
      | (x,0) := (x+1,0)
      | xy := xy
    end
  },
  goal := { boxes := list2d.add_to_line1 stor s.goal.boxes, }
}

def from_string_aux : list char → option (sokolevel × bool)
| [] := some ( ⟨ [], ⟨[], (0,0)⟩, ⟨[]⟩⟩ , ff)
| (c::str) := match (from_string_aux str), c with
  | none, _ := none
  | (some (s, sk_set)), '\n' := some (s.add_newline, sk_set)
  | (some (s, sk_set)), ' ' := some (s.add_newsquare tt ff ff ff, sk_set)
  | (some (s, sk_set)), '#' := some (s.add_newsquare ff ff ff ff, sk_set)
  | (some (s, sk_set)), '.' := some (s.add_newsquare tt ff tt ff, sk_set)
  | (some (s, sk_set)), '$' := some (s.add_newsquare tt tt ff ff, sk_set)
  | (some (s, sk_set)), '*' := some (s.add_newsquare tt tt tt ff, sk_set)
  | (some (s, ff)), '@' := some (s.add_newsquare tt ff ff tt, tt)
  | (some (s, ff)), '+' := some (s.add_newsquare tt ff tt tt, tt)
  | (some _), _ := none
  end

def from_string (str : string) : sokolevel :=
  match (from_string_aux str.to_list) with
  | none := default sokolevel
  | some (_, ff) := default sokolevel
  | some (level, tt) := level
  end

--                              _   
--    _____  ___ __   ___  _ __| |_ 
--   / _ \ \/ / '_ \ / _ \| '__| __|
--  |  __/>  <| |_) | (_) | |  | |_ 
--   \___/_/\_\ .__/ \___/|_|   \__|
--            |_|                   

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

instance : has_to_string sokolevel := ⟨λ s,
  list.as_string (to_string_aux2
  (s.avail.dfzip2d (s.ini.boxes.dfzip2d (s.goal.boxes.dfzip2d (list2d.set2d true [] s.ini.storekeeper)))))
⟩

instance : has_repr sokolevel
:= ⟨λ lev, (string.append (string.append "from_string \"" (to_string lev)) "\"")⟩

--       _                 _ _  __ _           _   _             
--   ___(_)_ __ ___  _ __ | (_)/ _(_) ___ __ _| |_(_) ___  _ __  
--  / __| | '_ ` _ \| '_ \| | | |_| |/ __/ _` | __| |/ _ \| '_ \ 
--  \__ \ | | | | | | |_) | | |  _| | (_| (_| | |_| | (_) | | | |
--  |___/_|_| |_| |_| .__/|_|_|_| |_|\___\__,_|\__|_|\___/|_| |_|
--                  |_|                                          

meta def soko_show : tactic unit :=
do
  `(sokolevel.solvable %%lev_e) ← tactic.target,
  lev ← tactic.eval_expr sokolevel lev_e,
  tactic.trace (to_string lev)

meta def soko_simp_root (e : expr) : tactic unit :=
do
  soko ← tactic.eval_expr sokolevel e,
  tactic.trace (to_string soko),
  let p : pexpr := ``(%%e = sokolevel.mk
    %%soko.avail (sokostate.mk %%soko.ini.boxes %%soko.ini.storekeeper) (boxes_only.mk %%soko.goal.boxes)),
  eq ← tactic.to_expr p,
  name ← tactic.get_unused_name,
  H ← tactic.assert name eq,
  tactic.reflexivity,
  tactic.rewrite_target H,
  tactic.clear H

meta def soko_simp : tactic unit :=
do
  `(sokolevel.solvable %%lev) ← tactic.target,
  soko_simp_root lev

meta def soko_check_depth : expr → ℕ → tactic unit
| _ 0 := return ()
| e (n+1) := do
  `(sokolevel.move %%lev _) ← return e,
  soko_check_depth lev n

meta def soko_simp_if_deep : tactic unit :=
do
  `(sokolevel.solvable %%lev) ← tactic.target,
  tactic.try ((soko_check_depth lev 20) >> (soko_simp_root lev))

meta def solve_up : tactic unit
:= tactic.apply `(solvable.move direction.up) >> soko_simp_if_deep
meta def solve_down : tactic unit
:= tactic.apply `(solvable.move direction.down) >> soko_simp_if_deep
meta def solve_left : tactic unit
:= tactic.apply `(solvable.move direction.left) >> soko_simp_if_deep
meta def solve_right : tactic unit
:= tactic.apply `(solvable.move direction.right) >> soko_simp_if_deep
meta def solve_finish : tactic unit
:= tactic.apply `(solvable.triv) >> tactic.apply `(@of_as_true) >> tactic.triv

end sokolevel
