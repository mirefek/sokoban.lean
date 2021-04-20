import .sokolevel
import .show_sokolevel

def lev := sokolevel.from_string "
#######
#. . .#
# $$$ #
#.$@$.#
# $$$ #
#. . .#
#######
"

#eval lev

example : lev.solvable :=
begin [show_sokolevel_w]
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_finish,
end
