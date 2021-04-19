import .sokolevel

def soko_level_29 := sokolevel.from_string "
#####              
#   ##             
# $  #########     
## # #       ######
## #   $#$#@  #   #
#  #      $ #   $ #
#  ### ######### ##
#  ## ..*..... # ##
## ## *.*..*.* # ##
# $########## ##$ #
#  $   $  $    $  #
#  #   #   #   #  #
###################
"

theorem solvable_level_29 : soko_level_29.solvable :=
begin
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_right,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_up,
  sokolevel.solve_left,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_up,
  sokolevel.solve_right,
  sokolevel.solve_right,
  sokolevel.solve_down,
  sokolevel.solve_down,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.solve_left,
  sokolevel.soko_simp,
  sokolevel.solve_up,
  sokolevel.soko_simp,
  sokolevel.solve_left,
  sokolevel.soko_simp,
  sokolevel.solve_down,
  sokolevel.soko_simp,
  sokolevel.solve_down,
  sokolevel.soko_simp,
  sokolevel.solve_finish
end