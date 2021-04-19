import tactic
import .direction
import .list2d
import .boolset2d
import .listdec

structure sokostate :=
(boxes : bset2d)
(storekeeper : ℕ × ℕ)

def sokostate.move (avail : bset2d) (d : direction) (s : sokostate)
  : sokostate :=
  let sk2 := d.shift s.storekeeper in
  if (sk2 ∉ avail) then s else
  if (sk2 ∉ s.boxes) then {
    boxes := s.boxes,
    storekeeper := sk2,
  }
  else
    let box2 := (d.shift sk2) in
    if box2 ∉ avail ∨ box2 ∈ s.boxes then s else {
      boxes := (s.boxes.remove sk2).add box2,
      storekeeper := sk2,
    }

structure sokostate.valid (avail : bset2d) (s : sokostate) : Prop :=
(boxes_avail : s.boxes ⊆ avail)
(sk_avail : s.storekeeper ∈ avail)
(sk_not_box : s.storekeeper ∉ s.boxes)

instance {avail : bset2d} {s : sokostate} : decidable (s.valid avail)
  :=
if Hb : s.boxes ⊆ avail then
  if Hska : s.storekeeper ∈ avail then
    if Hskb : s.storekeeper ∉ s.boxes then
      is_true ⟨Hb, Hska, Hskb⟩
    else is_false (λ H, Hskb H.sk_not_box)
  else is_false (λ H, Hska H.sk_avail)
else is_false (λ H, Hb H.boxes_avail)

inductive sokostate.reachable (avail : bset2d) (s2 : sokostate) : sokostate → Prop
| triv : sokostate.reachable s2
| move {s1 : sokostate} (d : direction) (H : sokostate.reachable (sokostate.move avail d s1))
  : sokostate.reachable s1

theorem sokostate.move_keep_valid {avail : bset2d} {s : sokostate} {d : direction}
  : s.valid avail → (s.move avail d).valid avail  :=
begin
  intro Hv,
  unfold sokostate.move, generalize E : d.shift s.storekeeper = sk2,
  by_cases Cska : sk2 ∈ avail, simp [Cska],
  by_cases Cskb: sk2 ∈ s.boxes, simp [Cskb],
  by_cases Cba : d.shift sk2 ∈ avail, simp [Cba],
  by_cases Cbb : d.shift sk2 ∈ s.boxes, simp [Cbb], exact Hv,
  { simp [Cbb], -- pushing a box
    split, simp, assume xy H,
    cases bset2d.of_mem_add H with Heq Hin,
    { rw Heq, exact Cba, },
    { exact Hv.boxes_avail xy (bset2d.mem_of_mem_remove Hin), },
    exact Cska,
    simp, apply bset2d.nmem_add_of_neq_nmem,
    { assume Heq, rw Heq at Cskb, exact Cbb Cskb, },
    { exact bset2d.nmem_remove, },
  }, { -- invalid push
    simp [Cba], exact Hv,
  }, { -- move a storekeeper
    simp [Cskb], split, exact Hv.boxes_avail,
    exact Cska,
    exact Cskb,
  }, { -- invalid move (to a wall)
    simp [Cska], exact Hv
  }
end

theorem sokostate.move_keep_box_count {avail : bset2d} {s : sokostate} {d : direction}
  : (s.move avail d).boxes.count = s.boxes.count
 :=
begin
  unfold sokostate.move, generalize E : d.shift s.storekeeper = sk2,
  by_cases Cska : sk2 ∈ avail, simp [Cska],
  by_cases Cskb: sk2 ∈ s.boxes, simp [Cskb],
  by_cases Cba : d.shift sk2 ∈ avail, simp [Cba],
  by_cases Cbb : d.shift sk2 ∈ s.boxes, simp [Cbb], {
    simp [Cbb],
    rw bset2d.count_add (bset2d.nmem_remove_of_nmem Cbb),
    exact bset2d.count_remove Cskb,
  },
  { simp [Cba]}, { simp [Cskb] }, { simp [Cska] },
end

theorem sokostate.reachable_keep_box_count {avail : bset2d} {s2 s : sokostate}
: reachable avail s2 s → s2.boxes.count = s.boxes.count
:=
begin
  assume H, induction H with s1 d H IH, refl,
  rw IH, exact sokostate.move_keep_box_count,
end

structure boxes_only :=
(boxes : bset2d)

def boxes_only.mem (s : sokostate) (bs : boxes_only)
  := s.boxes ⊆ bs.boxes ∧ bs.boxes ⊆ s.boxes
instance : has_mem sokostate boxes_only := ⟨boxes_only.mem⟩
lemma boxes_only.mem.unfold {s : sokostate} {bs : boxes_only}
  : s ∈ bs = (s.boxes ⊆ bs.boxes ∧ bs.boxes ⊆ s.boxes) := rfl

instance boxes_only.mem.decidable
  (s : sokostate) (bs : boxes_only) : decidable (s ∈ bs)
:= begin
  unfold has_mem.mem, unfold boxes_only.mem, apply_instance,
end
