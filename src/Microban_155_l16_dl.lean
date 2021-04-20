-- Deadlocks: var/Microban_155_l16/deadlocks
-- Levelset: data/Large Test Suite Sets/Microban_155.xsb
-- Level: 16

import .deadlocks

def Microban_155_l16 := sokolevel.from_string "
 ####     
 #  ####  
 #     ## 
## ##   # 
#. .# @$##
#   # $$ #
#  .#    #
##########
"

namespace Microban_155_l16
open deadlocks

@[reducible]
def deadlock_local (dl : boxint) : Prop := deadlock Microban_155_l16.avail Microban_155_l16.goal dl
def deadlocks_local (dls : list boxint) : Prop
:= dls.pall (λ dl, deadlock_local dl)
def generate_local : list (ℕ × ℕ) → list (ℕ × ℕ) → ℕ × ℕ → boxint
:= boxint.generate_from_list Microban_155_l16.avail

def dl0 := generate_local [(8,7)] [] (2,2)

theorem dl0_dl : deadlock_local dl0
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl0_dl.to_html

def dl1 := generate_local [(7,4), (8,6), (7,7)] [] (2,2)

theorem dl1_dl : deadlock_local dl1
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl0_dl, -- (7,7) right
end

#html dl1_dl.to_html

def dl2 := generate_local [(5,7)] [] (2,2)

theorem dl2_dl : deadlock_local dl2
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl2_dl.to_html

def dl3 := generate_local [(6,7)] [] (2,2)
def dl4 := generate_local [(7,7)] [] (2,2)
def dls3_4 := [dl3, dl4]

theorem dls3_4_dl : deadlocks_local dls3_4
:=
begin
  refine list.pall_iff.mpr (new_deadlocks _),
  rcases list.pall_in dls3_4 with ⟨dl3_in, dl4_in, irrelevant⟩,
  refine list.pall_iff.mp ⟨_, _, trivial⟩,
  {
    analyze_deadlock,
    deadlocked_step dl2_dl, -- (6,7) left
    deadlocked_step dl4_in, -- (6,7) right
  }, {
    analyze_deadlock,
    deadlocked_step dl3_in, -- (7,7) left
    deadlocked_step dl0_dl, -- (7,7) right
  },
end

theorem dl3_dl : deadlock_local dl3
:= dls3_4_dl.1
theorem dl4_dl : deadlock_local dl4
:= dls3_4_dl.2.1

#html dl3_dl.to_html
#html dl4_dl.to_html

def dl5 := generate_local [(8,6)] [] (2,2)

theorem dl5_dl : deadlock_local dl5
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl5_dl.to_html

def dl6 := generate_local [(6,3)] [] (2,2)

theorem dl6_dl : deadlock_local dl6
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl6_dl.to_html

def dl7 := generate_local [(7,4)] [] (2,2)

theorem dl7_dl : deadlock_local dl7
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl7_dl.to_html

def dl8 := generate_local [(5,3), (6,4), (7,5)] [] (5,4)

theorem dl8_dl : deadlock_local dl8
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl6_dl, -- (6,4) up
  deadlocked_step dl7_dl, -- (6,4) right
  deadlocked_step dl7_dl, -- (7,5) up
end

#html dl8_dl.to_html

#check dl8_dl

def dl9 := generate_local [(5,4), (6,4), (7,5)] [] (5,5)

theorem dl9_dl : deadlock_local dl9
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl8_dl, -- (5,4) up
  deadlocked_step dl6_dl, -- (6,4) up
  deadlocked_step dl7_dl, -- (7,5) up
end

#html dl9_dl.to_html

def dl10 := generate_local [(6,4), (5,5), (7,5)] [] (6,5)

theorem dl10_dl : deadlock_local dl10
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl6_dl, -- (6,4) up
  deadlocked_step dl9_dl, -- (5,5) up
  deadlocked_step dl7_dl, -- (7,5) up
end

#html dl10_dl.to_html

def dl11 := generate_local [(1,5), (3,7)] [(3,5)] (2,2)

theorem dl11_dl : deadlock_local dl11
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl11_dl.to_html

def dl12 := generate_local [(3,5), (2,6), (3,7)] [] (2,2)
def dl13 := generate_local [(3,5), (3,7)] [(1,5), (2,5), (1,6), (2,6)] (2,2)
def dl14 := generate_local [(2,5), (3,5), (3,7)] [] (2,2)
def dl15 := generate_local [(2,5), (3,5), (3,7)] [] (1,5)
def dls12_15 := [dl12, dl13, dl14, dl15]

theorem dls12_15_dl : deadlocks_local dls12_15
:=
begin
  refine list.pall_iff.mpr (new_deadlocks _),
  rcases list.pall_in dls12_15 with ⟨dl12_in, dl13_in, dl14_in, dl15_in, irrelevant⟩,
  refine list.pall_iff.mp ⟨_, _, _, _, trivial⟩,
  {
    analyze_deadlock,
    deadlocked_step dl15_in, -- (2,6) up
    deadlocked_step dl13_in, -- (2,6) down
    deadlocked_step dl13_in, -- (2,6) right
  }, {
    analyze_deadlock,
    deadlocked_step dl14_in, -- (2,4) down
  }, {
    analyze_deadlock,
    deadlocked_step dl12_in, -- (2,5) down
  }, {
    analyze_deadlock,
    deadlocked_step dl13_in, -- (2,5) up
  },
end

theorem dl12_dl : deadlock_local dl12
:= dls12_15_dl.1
theorem dl13_dl : deadlock_local dl13
:= dls12_15_dl.2.1
theorem dl14_dl : deadlock_local dl14
:= dls12_15_dl.2.2.1
theorem dl15_dl : deadlock_local dl15
:= dls12_15_dl.2.2.2.1

#html dl12_dl.to_html
#html dl13_dl.to_html
#html dl14_dl.to_html
#html dl15_dl.to_html

def dl16 := generate_local [(2,5), (2,6)] [] (2,2)

theorem dl16_dl : deadlock_local dl16
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl16_dl.to_html

def dl17 := generate_local [(1,7)] [] (2,2)

theorem dl17_dl : deadlock_local dl17
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#html dl17_dl.to_html

def dl18 := generate_local [(1,6), (2,7)] [] (2,2)

theorem dl18_dl : deadlock_local dl18
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl17_dl, -- (1,6) down
  deadlocked_step dl17_dl, -- (2,7) left
end

#html dl18_dl.to_html

def dl19 := generate_local [(3,5), (2,6), (2,7)] [] (3,6)

theorem dl19_dl : deadlock_local dl19
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl18_dl, -- (2,6) left
  deadlocked_step dl17_dl, -- (2,7) left
end

#html dl19_dl.to_html

def dl20 := generate_local [(2,5), (3,5), (2,7)] [] (2,2)
def dl21 := generate_local [(3,5), (2,7)] [(1,5), (2,5), (1,6), (2,6)] (2,2)
def dl22 := generate_local [(3,5), (2,6), (2,7)] [] (2,2)
def dls20_22 := [dl20, dl21, dl22]

theorem dls20_22_dl : deadlocks_local dls20_22
:=
begin
  refine list.pall_iff.mpr (new_deadlocks _),
  rcases list.pall_in dls20_22 with ⟨dl20_in, dl21_in, dl22_in, irrelevant⟩,
  refine list.pall_iff.mp ⟨_, _, _, trivial⟩,
  {
    analyze_deadlock,
    deadlocked_step dl22_in, -- (2,5) down
  }, {
    analyze_deadlock,
    deadlocked_step dl17_dl, -- (2,7) left
    deadlocked_step dl13_dl, -- (2,7) right
    deadlocked_step dl20_in, -- (2,4) down
  }, {
    analyze_deadlock,
    deadlocked_step dl21_in, -- (2,6) right
    deadlocked_step dl12_dl, -- (2,7) right
  },
end

#check dls20_22_dl

theorem dl20_dl : deadlock_local dl20
:= dls20_22_dl.1
theorem dl21_dl : deadlock_local dl21
:= dls20_22_dl.2.1
theorem dl22_dl : deadlock_local dl22
:= dls20_22_dl.2.2.1

#html dl20_dl.to_html
#html dl21_dl.to_html
#html dl22_dl.to_html

def dl23 := generate_local [(2,6), (3,7)] [(1,5), (2,5), (3,5), (1,6)] (2,2)
def dl24 := generate_local [(2,5), (2,7)] [(1,5), (3,5), (1,6), (2,6)] (2,2)
def dl25 := generate_local [(1,6), (3,7)] [(1,5), (2,5), (3,5), (2,6)] (2,2)
def dl26 := generate_local [(3,7)] [(1,5), (2,5), (3,5), (1,6), (2,6)] (2,2)
def dl27 := generate_local [(1,6), (2,6), (3,7)] [] (2,2)
def dl28 := generate_local [(2,6), (2,7)] [(1,5), (2,5), (3,5), (1,6)] (2,2)
def dl29 := generate_local [(2,5), (3,7)] [(1,5), (3,5), (1,6), (2,6)] (2,2)
def dl30 := generate_local [(2,5), (3,7)] [(1,5), (3,5), (1,6), (2,6)] (1,5)
def dl31 := generate_local [(2,5), (1,6), (3,7)] [] (2,2)
def dl32 := generate_local [(2,7)] [(1,5), (2,5), (3,5), (1,6), (2,6)] (2,2)
def dls23_32 := [dl23, dl24, dl25, dl26, dl27, dl28, dl29, dl30, dl31, dl32]

theorem dls23_32_dl : deadlocks_local dls23_32
:=
begin
  refine list.pall_iff.mpr (new_deadlocks _),
  rcases list.pall_in dls23_32 with ⟨dl23_in, dl24_in, dl25_in, dl26_in, dl27_in, dl28_in, dl29_in, dl30_in, dl31_in, dl32_in, irrelevant⟩,
  refine list.pall_iff.mp ⟨_, _, _, _, _, _, _, _, _, _, trivial⟩,
  {
    analyze_deadlock,
    deadlocked_step dl30_in, -- (2,6) up
    deadlocked_step dl32_in, -- (2,6) down
    deadlocked_step dl25_in, -- (2,6) left
    deadlocked_step dl26_in, -- (2,6) right
    deadlocked_step dl16_dl, -- (2,4) down
  }, {
    analyze_deadlock,
    deadlocked_step dl28_in, -- (2,5) down
  }, {
    analyze_deadlock,
    deadlocked_step dl11_dl, -- (1,6) up
    deadlocked_step dl26_in, -- (1,6) down
    deadlocked_step dl31_in, -- (2,4) down
  }, {
    analyze_deadlock,
    deadlocked_step dl29_in, -- (2,4) down
  }, {
    analyze_deadlock,
    deadlocked_step dl23_in, -- (1,6) down
    deadlocked_step dl25_in, -- (2,6) down
  }, {
    analyze_deadlock,
    deadlocked_step dl18_dl, -- (2,6) left
    deadlocked_step dl32_in, -- (2,6) right
    deadlocked_step dl17_dl, -- (2,7) left
    deadlocked_step dl23_in, -- (2,7) right
    deadlocked_step dl16_dl, -- (2,4) down
    deadlocked_step dl19_dl, -- (3,6) up
  }, {
    analyze_deadlock,
    deadlocked_step dl23_in, -- (2,5) down
  }, {
    analyze_deadlock,
    deadlocked_step dl26_in, -- (2,5) up
    deadlocked_step dl11_dl, -- (2,5) left
    deadlocked_step dl13_dl, -- (2,5) right
  }, {
    analyze_deadlock,
    deadlocked_step dl27_in, -- (2,5) down
  }, {
    analyze_deadlock,
    deadlocked_step dl17_dl, -- (2,7) left
    deadlocked_step dl26_in, -- (2,7) right
    deadlocked_step dl24_in, -- (2,4) down
    deadlocked_step dl21_dl, -- (3,6) up
  },
end

theorem dl23_dl : deadlock_local dl23
:= dls23_32_dl.1
theorem dl24_dl : deadlock_local dl24
:= dls23_32_dl.2.1
theorem dl25_dl : deadlock_local dl25
:= dls23_32_dl.2.2.1
theorem dl26_dl : deadlock_local dl26
:= dls23_32_dl.2.2.2.1
theorem dl27_dl : deadlock_local dl27
:= dls23_32_dl.2.2.2.2.1
theorem dl28_dl : deadlock_local dl28
:= dls23_32_dl.2.2.2.2.2.1
theorem dl29_dl : deadlock_local dl29
:= dls23_32_dl.2.2.2.2.2.2.1
theorem dl30_dl : deadlock_local dl30
:= dls23_32_dl.2.2.2.2.2.2.2.1
theorem dl31_dl : deadlock_local dl31
:= dls23_32_dl.2.2.2.2.2.2.2.2.1
theorem dl32_dl : deadlock_local dl32
:= dls23_32_dl.2.2.2.2.2.2.2.2.2.1

#html dl23_dl.to_html
#html dl24_dl.to_html
#html dl25_dl.to_html
#html dl26_dl.to_html
#html dl27_dl.to_html
#html dl28_dl.to_html
#html dl29_dl.to_html
#html dl30_dl.to_html
#html dl31_dl.to_html
#html dl32_dl.to_html

end Microban_155_l16
