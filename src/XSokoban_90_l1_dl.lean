-- Deadlocks: var/XSokoban_90_l1/deadlocks
-- Levelset: data/Large Test Suite Sets/XSokoban_90.xsb
-- Level: 1

import .deadlocks

def XSokoban_90_l1 := sokolevel.from_string "
    #####          
    #   #          
    #$  #          
  ###  $##         
  #  $ $ #         
### # ## #   ######
#   # ## #####  ..#
# $  $          ..#
##### ### #@##  ..#
    #     #########
    #######        
"

namespace XSokoban_90_l1
open deadlocks

@[reducible]
def deadlock_local (dl : boxint) : Prop := deadlock XSokoban_90_l1.avail XSokoban_90_l1.goal dl
def deadlocks_local (dls : list boxint) : Prop
:= dls.pall (λ dl, deadlock_local dl)
def generate_local : list (ℕ × ℕ) → list (ℕ × ℕ) → ℕ × ℕ → boxint
:= boxint.generate_from_list XSokoban_90_l1.avail

def dl0 := generate_local [(8,5)] [] (5,2)

theorem dl0_dl : deadlock_local dl0
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl0_dl

def dl1 := generate_local [(3,5)] [] (5,2)

theorem dl1_dl : deadlock_local dl1
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl1_dl

def dl2 := generate_local [(14,9)] [] (5,2)

theorem dl2_dl : deadlock_local dl2
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl2_dl

def dl3 := generate_local [(5,10)] [] (5,2)

theorem dl3_dl : deadlock_local dl3
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl3_dl

def dl4 := generate_local [(6,5), (7,5)] [] (5,2)

theorem dl4_dl : deadlock_local dl4
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl4_dl

def dl5 := generate_local [(15,9), (16,9)] [] (5,2)

theorem dl5_dl : deadlock_local dl5
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl5_dl

def dl6 := generate_local [(5,2)] [] (6,2)

theorem dl6_dl : deadlock_local dl6
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl6_dl

def dl7 := generate_local [(1,8)] [] (5,2)

theorem dl7_dl : deadlock_local dl7
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl7_dl

def dl8 := generate_local [(7,2)] [] (5,2)

theorem dl8_dl : deadlock_local dl8
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl8_dl

def dl9 := generate_local [(5,5), (6,5), (5,6)] [] (5,2)

theorem dl9_dl : deadlock_local dl9
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl9_dl

def dl10 := generate_local [(5,4), (5,5), (6,5)] [] (5,2)

theorem dl10_dl : deadlock_local dl10
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl10_dl

def dl11 := generate_local [(5,4), (5,5), (7,5)] [] (3,5)

theorem dl11_dl : deadlock_local dl11
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl4_dl, -- (5,5) right
  deadlocked_step dl10_dl, -- (7,5) left
end

#check dl11_dl

def dl12 := generate_local [(5,6), (5,7)] [] (5,2)

theorem dl12_dl : deadlock_local dl12
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl12_dl

def dl13 := generate_local [(5,5), (6,5), (5,7)] [] (5,2)

theorem dl13_dl : deadlock_local dl13
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl12_dl, -- (5,5) down
  deadlocked_step dl9_dl, -- (5,7) up
end

#check dl13_dl

def dl14 := generate_local [(5,3), (5,4)] [] (5,2)

theorem dl14_dl : deadlock_local dl14
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl14_dl

def dl15 := generate_local [(5,4), (7,4), (6,5), (5,6)] [] (5,2)

theorem dl15_dl : deadlock_local dl15
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl9_dl, -- (5,4) down
  deadlocked_step dl4_dl, -- (7,4) down
end

#check dl15_dl

def dl16 := generate_local [(5,5), (7,5), (5,6)] [] (3,5)

theorem dl16_dl : deadlock_local dl16
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl4_dl, -- (5,5) right
  deadlocked_step dl9_dl, -- (7,5) left
end

#check dl16_dl

def dl17 := generate_local [(5,5), (7,5), (5,7)] [] (3,5)

theorem dl17_dl : deadlock_local dl17
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl4_dl, -- (5,5) right
  deadlocked_step dl13_dl, -- (7,5) left
  deadlocked_step dl16_dl, -- (5,7) up
end

#check dl17_dl

def dl18 := generate_local [(4,5), (7,5), (5,7), (5,8)] [] (5,2)

theorem dl18_dl : deadlock_local dl18
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl1_dl, -- (4,5) left
  deadlocked_step dl0_dl, -- (7,5) right
end

#check dl18_dl

def dl19 := generate_local [(4,5), (7,5), (5,6), (5,8)] [] (5,2)

theorem dl19_dl : deadlock_local dl19
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl1_dl, -- (4,5) left
  deadlocked_step dl0_dl, -- (7,5) right
  deadlocked_step dl18_dl, -- (5,6) down
end

#check dl19_dl

def dl20 := generate_local [(4,5), (5,5), (5,6)] [] (5,2)

theorem dl20_dl : deadlock_local dl20
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl20_dl

def dl21 := generate_local [(4,5), (5,5), (5,7)] [] (5,2)

theorem dl21_dl : deadlock_local dl21
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl12_dl, -- (5,5) down
  deadlocked_step dl20_dl, -- (5,7) up
end

#check dl21_dl

def dl22 := generate_local [(2,8), (3,8)] [] (5,2)

theorem dl22_dl : deadlock_local dl22
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl22_dl

def dl23 := generate_local [(4,5), (2,8), (4,8)] [] (5,2)

theorem dl23_dl : deadlock_local dl23
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl1_dl, -- (4,5) left
  deadlocked_step dl22_dl, -- (4,8) left
end

#check dl23_dl

def dl24 := generate_local [(5,7), (4,8), (5,8)] [] (5,2)

theorem dl24_dl : deadlock_local dl24
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl24_dl

def dl25 := generate_local [(5,6), (4,8), (5,8)] [] (5,2)

theorem dl25_dl : deadlock_local dl25
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl24_dl, -- (5,6) down
  deadlocked_step dl12_dl, -- (5,8) up
end

#check dl25_dl

def dl26 := generate_local [(5,4), (4,5), (5,5)] [] (5,2)

theorem dl26_dl : deadlock_local dl26
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl26_dl

def dl27 := generate_local [(4,5), (5,5), (7,5), (5,8)] [] (5,2)

theorem dl27_dl : deadlock_local dl27
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl19_dl, -- (5,5) down
  deadlocked_step dl0_dl, -- (7,5) right
end

#check dl27_dl

def dl28 := generate_local [(4,5), (5,7), (2,8), (5,8)] [] (5,2)

theorem dl28_dl : deadlock_local dl28
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl1_dl, -- (4,5) left
  deadlocked_step dl23_dl, -- (5,8) left
end

#check dl28_dl

def dl29 := generate_local [(4,5), (5,6), (2,8), (5,8)] [] (5,2)

theorem dl29_dl : deadlock_local dl29
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl1_dl, -- (4,5) left
  deadlocked_step dl28_dl, -- (5,6) down
  deadlocked_step dl12_dl, -- (5,8) up
  deadlocked_step dl23_dl, -- (5,8) left
end

#check dl29_dl

def dl30 := generate_local [(3,8), (4,8)] [] (5,2)

theorem dl30_dl : deadlock_local dl30
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl30_dl

def dl31 := generate_local [(14,7)] [] (5,2)

theorem dl31_dl : deadlock_local dl31
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl31_dl

def dl32 := generate_local [(5,4), (5,5), (2,8), (4,8)] [] (5,2)

theorem dl32_dl : deadlock_local dl32
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl23_dl, -- (5,5) left
  deadlocked_step dl22_dl, -- (4,8) left
end

#check dl32_dl

def dl33 := generate_local [(5,5), (5,6), (2,8), (4,8)] [] (5,2)

theorem dl33_dl : deadlock_local dl33
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl23_dl, -- (5,5) left
  deadlocked_step dl22_dl, -- (4,8) left
end

#check dl33_dl

def dl34 := generate_local [(6,8), (7,8)] [] (5,2)

theorem dl34_dl : deadlock_local dl34
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl34_dl

def dl35 := generate_local [(7,8), (8,8)] [] (5,2)

theorem dl35_dl : deadlock_local dl35
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl35_dl

def dl36 := generate_local [(6,8), (8,8)] [] (5,2)

theorem dl36_dl : deadlock_local dl36
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl35_dl, -- (6,8) right
  deadlocked_step dl34_dl, -- (8,8) left
end

#check dl36_dl

def dl37 := generate_local [(5,7), (5,8), (8,8)] [] (5,2)

theorem dl37_dl : deadlock_local dl37
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl36_dl, -- (5,8) right
end

#check dl37_dl

def dl38 := generate_local [(5,6), (5,8), (8,8)] [] (5,2)

theorem dl38_dl : deadlock_local dl38
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl37_dl, -- (5,6) down
  deadlocked_step dl36_dl, -- (5,8) right
end

#check dl38_dl

def dl39 := generate_local [(4,5), (5,5), (5,8), (8,8)] [] (5,2)

theorem dl39_dl : deadlock_local dl39
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl38_dl, -- (5,5) down
end

#check dl39_dl

def dl40 := generate_local [(5,7), (5,8), (6,8)] [] (5,2)

theorem dl40_dl : deadlock_local dl40
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl40_dl

def dl41 := generate_local [(5,7), (5,8), (7,8)] [] (5,2)

theorem dl41_dl : deadlock_local dl41
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl34_dl, -- (5,8) right
  deadlocked_step dl40_dl, -- (7,8) left
end

#check dl41_dl

def dl42 := generate_local [(5,6), (5,8), (6,8)] [] (5,2)

theorem dl42_dl : deadlock_local dl42
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl40_dl, -- (5,6) down
  deadlocked_step dl12_dl, -- (5,8) up
end

#check dl42_dl

def dl43 := generate_local [(5,6), (5,8), (7,8)] [] (5,2)

theorem dl43_dl : deadlock_local dl43
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl41_dl, -- (5,6) down
  deadlocked_step dl12_dl, -- (5,8) up
  deadlocked_step dl34_dl, -- (5,8) right
  deadlocked_step dl42_dl, -- (7,8) left
end

#check dl43_dl

def dl44 := generate_local [(5,6), (5,8), (8,8)] [] (14,7)

theorem dl44_dl : deadlock_local dl44
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl12_dl, -- (5,8) up
  deadlocked_step dl43_dl, -- (8,8) left
end

#check dl44_dl

def dl45 := generate_local [(5,6), (5,8), (9,8)] [] (14,7)

theorem dl45_dl : deadlock_local dl45
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl44_dl, -- (9,8) left
end

#check dl45_dl

def dl46 := generate_local [(5,6), (5,8), (10,8)] [] (14,7)

theorem dl46_dl : deadlock_local dl46
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl45_dl, -- (10,8) left
end

#check dl46_dl

def dl47 := generate_local [(5,6), (5,8), (11,8)] [] (14,7)

theorem dl47_dl : deadlock_local dl47
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl46_dl, -- (11,8) left
end

#check dl47_dl

def dl48 := generate_local [(5,6), (5,8), (12,8)] [] (14,7)

theorem dl48_dl : deadlock_local dl48
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl47_dl, -- (12,8) left
end

#check dl48_dl

def dl49 := generate_local [(5,6), (5,8), (13,8)] [] (14,7)

theorem dl49_dl : deadlock_local dl49
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl48_dl, -- (13,8) left
end

#check dl49_dl

def dl50 := generate_local [(5,6), (5,8), (14,8)] [] (14,7)

theorem dl50_dl : deadlock_local dl50
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl31_dl, -- (14,8) up
  deadlocked_step dl2_dl, -- (14,8) down
  deadlocked_step dl49_dl, -- (14,8) left
end

#check dl50_dl

def dl51 := generate_local [(5,5), (5,6), (2,8), (5,8)] [] (5,2)

theorem dl51_dl : deadlock_local dl51
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl29_dl, -- (5,5) left
  deadlocked_step dl12_dl, -- (5,8) up
  deadlocked_step dl33_dl, -- (5,8) left
end

#check dl51_dl

def dl52 := generate_local [(5,7), (3,8), (5,8)] [] (5,2)

theorem dl52_dl : deadlock_local dl52
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl24_dl, -- (3,8) right
  deadlocked_step dl30_dl, -- (5,8) left
end

#check dl52_dl

def dl53 := generate_local [(5,6), (3,8), (5,8)] [] (5,2)

theorem dl53_dl : deadlock_local dl53
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl52_dl, -- (5,6) down
  deadlocked_step dl25_dl, -- (3,8) right
  deadlocked_step dl12_dl, -- (5,8) up
  deadlocked_step dl30_dl, -- (5,8) left
end

#check dl53_dl

def dl54 := generate_local [(5,4), (7,4), (6,5), (5,7)] [] (5,2)

theorem dl54_dl : deadlock_local dl54
:=
begin
  apply new_deadlock,
  analyze_deadlock,
  deadlocked_step dl13_dl, -- (5,4) down
  deadlocked_step dl4_dl, -- (7,4) down
end

#check dl54_dl

def dl55 := generate_local [(15,7), (16,7)] [] (5,2)

theorem dl55_dl : deadlock_local dl55
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

#check dl55_dl

end XSokoban_90_l1
