import .deadlocks

namespace deadlocks_example
open deadlocks

def lev := sokolevel.from_string "
######
#    #
# $@ #
# .  #
######
"

@[reducible]
def deadlock_local (dl : boxint) : Prop := deadlock lev.avail lev.goal dl
def deadlocks_local (dls : list boxint) : Prop
:= dls.pall (λ dl, deadlock_local dl)
def generate_local : list (ℕ × ℕ) → list (ℕ × ℕ) → ℕ × ℕ → boxint
:= boxint.generate_from_list lev.avail

def dl0 := generate_local [(1,2)] [] (2,2)

theorem dl0_dl : deadlock_local dl0
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

def dl1 := generate_local [(4,2)] [] (1,2)

theorem dl1_dl : deadlock_local dl1
:=
begin
  apply new_deadlock,
  analyze_deadlock,
end

def dl2 := generate_local [(2,2)] [] (1,2)
def dl3 := generate_local [(3,2)] [] (1,2)
def dl2_3 := [dl2, dl3]

theorem dl2_3_dl : deadlocks_local dl2_3
:=
begin
  refine list.pall_iff.mpr (new_deadlocks _),
  rcases list.pall_in dl2_3 with ⟨dl2_in, dl3_in, irrelevant⟩,
  refine list.pall_iff.mp ⟨_, _, trivial⟩,
  {
    analyze_deadlock,
    deadlocked_step dl0_dl,
    deadlocked_step dl3_in,
  }, {
    analyze_deadlock,
    deadlocked_step dl2_in,
    deadlocked_step dl1_dl,
  },
end

theorem dl2_dl : deadlock_local dl2
:= dl2_3_dl.1
theorem dl3_dl : deadlock_local dl3
:= dl2_3_dl.2.1

end deadlocks_example
