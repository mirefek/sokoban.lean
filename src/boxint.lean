import tactic
import .direction
import .list2d
import .boolset2d
import .component2d
import .sokostate

structure boxint := 
(subboxes : bset2d)
(supboxes : bset2d)
(sk_comp : bset2d)

structure boxint.valid (avail : bset2d) (as : boxint) : Prop :=
(sub_sup : as.subboxes ⊆ as.supboxes)
(sup_avail : as.supboxes ⊆ avail)
(sub_disj : as.subboxes.disjoint as.sk_comp)
(sk_comp_avail : as.sk_comp ⊆ avail)
(sk_comp_closed : ∀ xy ∈ as.sk_comp, ∀ d : direction,
  d.shift xy ∈ avail →
  (d.shift xy ∈ as.sk_comp ∨ d.shift xy ∈ as.subboxes))

def boxint.mem (s : sokostate) (as : boxint)
  := s.storekeeper ∈ as.sk_comp ∧
     as.subboxes ⊆ s.boxes ∧ s.boxes ⊆ as.supboxes
instance : has_mem sokostate boxint
:= ⟨boxint.mem⟩
lemma boxint.mem.unfold
  {s : sokostate} {as : boxint}
  : s ∈ as = (s.storekeeper ∈ as.sk_comp ∧
     as.subboxes ⊆ s.boxes ∧ s.boxes ⊆ as.supboxes)
:= rfl
instance boxint.mem.decidable
  (s : sokostate) (as : boxint) : decidable (s ∈ as)
:= begin
  unfold has_mem.mem, unfold boxint.mem, apply_instance,
end


def boxint.disjoint
  (as1 : boxint) (as2 : boxes_only) : Prop
  := ¬ (as1.subboxes ⊆ as2.boxes ∧ as2.boxes ⊆ as1.supboxes)
lemma boxint.disjoint_correct
  (as : boxint) (bs : boxes_only)
  (s : sokostate)
  : as.disjoint bs → s ∈ as → s ∈ bs → false :=
begin
  simp [boxint.mem.unfold, boxes_only.mem.unfold, boxint.disjoint],
  introv Hnsol Hsk Hsub Hsup Hsbs Hbss,
  exact Hnsol (bset2d.subset.trans Hsub Hsbs) (bset2d.subset.trans Hbss Hsup),
end
instance boxint.disjoint.decidable
  (as : boxint) (bs : boxes_only) : decidable (as.disjoint bs)
:= begin
  unfold boxint.disjoint, apply_instance,
end

def boxint.subset (as1 as2 : boxint) : Prop
  := as1.sk_comp ⊆ as2.sk_comp ∧ as2.subboxes ⊆ as1.subboxes
  ∧ as1.supboxes ⊆ as2.supboxes
instance : has_subset boxint := ⟨boxint.subset⟩

lemma boxint.subset_correct (as1 as2 : boxint)
  : as1 ⊆ as2 → ∀ s : sokostate, s ∈ as1 → s ∈ as2 :=
begin
  intros H12 s H1,
  rcases H12 with ⟨H12sk,H12sub,H12sup⟩,
  rcases H1 with ⟨H1sk,H1sub,H1sup⟩,
  split, exact H12sk _ H1sk,
  split, exact bset2d.subset.trans H12sub H1sub,
  exact bset2d.subset.trans H1sup H12sup,
end
instance boxint.subset.decidable
  (as1 as2 : boxint) : decidable (as1 ⊆ as2)
:= begin
  unfold has_subset.subset, unfold boxint.subset, apply_instance,
end

def boxint.subset_g (as1 as2 : boxint) (goal : boxes_only) : Prop
  := as1.sk_comp ⊆ as2.sk_comp ∧ as2.subboxes ⊆ as1.subboxes
  ∧ ( as1.supboxes ⊆ as2.supboxes ∨
    goal.boxes.count ≤ as1.subboxes.count ∧ as1.subboxes ⊆ as2.supboxes )
lemma boxint.subset_g_correct {avail : bset2d} {as1 as2 : boxint} {goal : boxes_only}
: as1.subset_g as2 goal → ∀ s sg : sokostate,
s ∈ as1 → sg ∈ goal → sg.reachable avail s → s ∈ as2
:=
begin
  intros H12 s sg H1 Hg Hr,
  rcases H12 with ⟨H12sk, H12sub, H12sup_cnt⟩,
  rcases H1 with ⟨H1sk,H1sub, H1sup⟩,
  split, exact H12sk _ H1sk,
  split, exact bset2d.subset.trans H12sub H1sub,
  cases H12sup_cnt with H12sup H12sup_cnt,
    exact bset2d.subset.trans H1sup H12sup,
  { cases H12sup_cnt with H_cnt H12sup,
    have : sg.boxes.count = s.boxes.count := sokostate.reachable_keep_box_count Hr,
    have : as1.subboxes.count ≤ s.boxes.count := bset2d.count_le_of_subset _ _ H1sub,
    have : sg.boxes.count ≤ goal.boxes.count := bset2d.count_le_of_subset _ _ Hg.1,
    have : as1.subboxes.count = s.boxes.count, by omega,
    have : s.boxes ⊆ as1.subboxes := bset2d.subset_eq_of_count_eq _ _ H1sub this,
    exact bset2d.subset.trans this H12sup,
  }
end
instance boxint.subset_g.decidable
  (as1 as2 : boxint) (goal : boxes_only) : decidable (as1.subset_g as2 goal)
:= begin
  unfold boxint.subset_g, apply_instance,
end

def boxint.generate (avail : bset2d) (subboxes supboxes : bset2d) (sk : ℕ × ℕ) : boxint
  := {
    subboxes := subboxes,
    supboxes := supboxes,
    sk_comp := component2d (avail \ subboxes) (bset2d.from_index sk),
  }

theorem boxint.generate_valid {avail subboxes supboxes : bset2d} {sk : ℕ × ℕ}
  : subboxes ⊆ supboxes → supboxes ⊆ avail →
  (boxint.generate avail subboxes supboxes sk).valid avail :=
begin
  intros sub_sup sup_avail, split, exact sub_sup, exact sup_avail, {
    intros xy Hsub Hcomp,
    exact bset2d.nmem_of_mem_sdiff (component2d_subset_avail xy Hcomp) Hsub,
  }, {
    intros xy Hcomp,
    exact bset2d.mem_of_mem_sdiff (component2d_subset_avail xy Hcomp),
  }, {
    introv Hcomp Ha2, by_cases C : d.shift xy ∈ subboxes,
    { right, exact C, }, left,
    have Ha2 : d.shift xy ∈ avail \ subboxes
      := bset2d.mem_sdiff_of_mem_nmem Ha2 C,
    exact component2d_closed Hcomp Ha2,
  },
end

def boxint.get_pushes (avail : bset2d) (s : boxint)
  : list (direction × (ℕ × ℕ))
  := do
  box ← s.subboxes.to_indexes,
  d ← direction.luniv,
  if d.shift box ∈ avail ∧ d.shift box ∉ s.subboxes
    ∧ d.opposite.shift box ∈ s.sk_comp
  then return (d, box)
  else list.nil

def boxint.get_appearances (avail : bset2d) (s : boxint)
  : list (direction × (ℕ × ℕ))
  := do
  box ← (avail \ s.supboxes).to_indexes,
  d ← direction.luniv,
  if d.shift box ∈ s.supboxes ∧ d.shift box ∉ s.subboxes
    ∧ d.shift (d.shift box) ∈ s.sk_comp
    ∧ d.shift (d.shift box) ≠ d.shift box
  then return (d.opposite, d.shift box)
  else list.nil

def boxint.get_moves (avail : bset2d) (as : boxint)
  : list (direction × (ℕ × ℕ))
  := boxint.get_pushes avail as ++ boxint.get_appearances avail as

lemma boxint.in_get_moves_iff (avail : bset2d) (s : boxint) (Hv : s.valid avail)
  : ∀ (d : direction) (box : ℕ×ℕ),
  (d,box) ∈ boxint.get_moves avail s ↔ (
    d.opposite.shift box ∈ s.sk_comp ∧
    d.opposite.shift box ≠ box ∧
    d.shift box ∈ avail ∧ d.shift box ∉ s.subboxes ∧
    box ∈ s.supboxes ∧ (d.shift box ∈ s.supboxes → box ∈ s.subboxes)
  ) :=
begin
  intros, unfold boxint.get_moves, rw list.mem_append,
  split, {
    rename box box', rename d d',
    intro H, cases H, {
      unfold boxint.get_pushes at H, simp [-prod.exists] at H,
      rcases H with ⟨box,Hbox,d,Huniv,H⟩, clear Huniv,
      have Hbox := (bset2d.to_indexes_iff _ _).mp Hbox,
      by_cases C : d.shift box ∈ avail ∧ d.shift box ∉ s.subboxes
          ∧ d.opposite.shift box ∈ s.sk_comp, {
        simp [C] at H, rw [H.1, H.2], clear H,
        rcases C with ⟨Ha2, Hnb2, Hsk⟩,
        split, exact Hsk,
        split, { -- disproving border case
          assume Heq, rw Heq at Hsk,
          exact Hv.sub_disj box Hbox Hsk,
        },
        split, exact Ha2, split, exact Hnb2,
        split, exact Hv.sub_sup box Hbox,
        intro, exact Hbox,
      }, { simp [C] at H, exact false.elim H, },
    }, {
      unfold boxint.get_appearances at H, simp [-prod.exists] at H,
      rcases H with ⟨box,Hbox,d,Huniv,H⟩, clear Huniv,
      have Hbox := (bset2d.to_indexes_iff _ box).mp Hbox,
      have Hba: box ∈ avail, from bset2d.mem_of_mem_sdiff Hbox,
      have Hbnsup: box ∉ s.supboxes, from bset2d.nmem_of_mem_sdiff Hbox,
      by_cases C : d.shift box ∈ s.supboxes ∧ d.shift box ∉ s.subboxes
          ∧ d.shift (d.shift box) ∈ s.sk_comp ∧ d.shift (d.shift box) ≠ d.shift box, {
        simp [C] at H, rw [H.1, H.2], clear H,
        rcases C with ⟨Hsup2, Hfree, Hcomp, Hnngen⟩,
        cases direction.opposite_shift d box with Heq Hop_simp, {
          -- border case d.shift box = box
          simp [Heq] at Hnngen, exact false.elim Hnngen,
        }, {
          rw [Hop_simp, direction.opposite_opposite],
          split, exact Hcomp,
          split, exact Hnngen,
          split, exact Hba,
          split, exact mt (Hv.sub_sup box) Hbnsup,
          split, exact Hsup2,
          assume Hbsup, exact false.elim (Hbnsup Hbsup),
        }
      },
      { simp [C] at H, exact false.elim H, }
    }
  }, {
    rintros ⟨Hcomp, Hnngen, Hav, Hfree, Hsup, H⟩,
    by_cases C : box ∈ s.subboxes, { left,
      unfold boxint.get_pushes, simp [-prod.exists], existsi box,
      split, exact (bset2d.to_indexes_iff s.subboxes box).mpr C,
      existsi d, split, exact direction.luniv_complete,
      simp [Hfree, Hcomp, Hav],
    }, { right,
      unfold boxint.get_appearances, simp [-prod.exists], existsi d.shift box,
      split, { show d.shift box ∈ (avail \ s.supboxes).to_indexes,
        apply (bset2d.to_indexes_iff _ _).mpr,
        apply bset2d.mem_sdiff_of_mem_nmem,
        exact Hav, assume H2, exact C (H H2),
      },
      existsi d.opposite,
      split, exact direction.luniv_complete,
      simp [direction.opposite_opposite],
      cases direction.opposite_shift d box with Heq Hop_simp, {
        -- border case, d.shift box = box
        rw Heq at H Hfree, exact false.elim (C (H Hsup)),
      },
      { rw Hop_simp, simp! [Hsup, C, Hcomp, Hnngen], }
    },
  }
end

def boxint.move (avail : bset2d)
  (s : boxint) (d : direction) (box : ℕ×ℕ)
  := boxint.generate avail
     ((s.subboxes.remove box).add (d.shift box))
     ((s.supboxes.remove box).add (d.shift box))
     box

def boxint.next_states (avail : bset2d) (s : boxint) : list boxint
  := list.map (function.uncurry (boxint.move avail s)) (boxint.get_moves avail s)

theorem boxint.next_valid (avail : bset2d) (as1 : boxint)
  : as1.valid avail →
  ∀ as2 : boxint, as2 ∈ as1.next_states avail → as2.valid avail
:=
begin
  introv Hv H, simp [boxint.next_states, -prod.exists] at H,
  rcases H with ⟨⟨d, box⟩, H, Heq⟩,
  simp at Heq, rw ←Heq, clear Heq as2,
  rw (boxint.in_get_moves_iff avail as1 Hv) at H,
  rcases H with ⟨Hcomp, Hnng, Hav, Hnb, Hsp, Hextra⟩,
  apply boxint.generate_valid, {
    apply bset2d.subset_add_same,
    apply bset2d.subset_remove_same,
    exact Hv.sub_sup,
  }, {
    assume xy, assume H,
    cases bset2d.of_mem_add H with H H,
    rw H, exact Hav,
    have := bset2d.mem_of_mem_remove H,
    exact Hv.sup_avail xy this,
  }
end

theorem boxint.next_of_real_move (avail : bset2d) (as1 : boxint) :
  as1.valid avail →
  ∀ (s : sokostate) (d : direction), s ∈ as1 → s.move avail d ∈ as1 ∨
  (∃ as2 : boxint, as2 ∈ as1.next_states avail ∧ s.move avail d ∈ as2)
:=
begin
  intros Hv s d Hin,
  have := Hin,
  rcases this with ⟨Hsk,Hsub,Hsup⟩,
  let box := d.shift s.storekeeper,
  let box2 := d.shift box,
  by_cases C : box ∈ s.boxes ∧ box2 ∈ avail ∧ box2 ∉ s.boxes
    ∧ (box ∈ as1.subboxes ∨ box2 ∉ as1.supboxes), {

    right, -- we move to another abstract state

    existsi as1.move avail d box,
    rcases C with ⟨Hbb, Hb2a, Hb2nb, Has⟩,
    split, { -- in next_states
      simp [boxint.next_states, -prod.exists],
      existsi (d,box), split, {
        apply (boxint.in_get_moves_iff avail as1 Hv d box).mpr,
        have Hngen : box ≠ s.storekeeper, {
          assume Heq, simp [box] at Heq,
          simp only [box,box2,Heq] at Hbb Hb2nb,
          exact false.elim (Hb2nb Hbb),
        },
        have : d.opposite.shift box = s.storekeeper
          := or.resolve_left (direction.opposite_shift d s.storekeeper) Hngen,
        rw this,
        split, exact Hsk,
        split, exact ne_comm.mp Hngen,
        split, exact Hb2a,
        split, exact mt (Hsub box2) Hb2nb,
        split, exact Hsup box Hbb,
        exact or.neg_resolve_right Has,
      }, refl,
    }, { -- emulates real move
      have Hba : box ∈ avail := Hv.sup_avail box (Hsup box Hbb),
      simp [boxint.move, boxint.generate],
      simp [sokostate.move, Hba, Hbb, Hb2a, Hb2nb],
      split, simp, {
        apply component2d_supset, {
          intros xy H,
          rw (bset2d.from_index_iff box xy).1 H, clear H xy,
          apply bset2d.mem_sdiff_of_mem_nmem Hba,
          apply bset2d.nmem_add_of_neq_nmem, {
            intro contra, rw contra at Hbb, exact Hb2nb Hbb,
          }, exact bset2d.nmem_remove,
        },
        exact (bset2d.from_index_iff box box).2 rfl,
      },
      simp, split, {
        apply bset2d.subset_add_same,
        apply bset2d.subset_remove_same,
        exact Hsub,
      },
      apply bset2d.subset_add_same,
      apply bset2d.subset_remove_same,
      exact Hsup,
    }
  },

  left, -- the abstract state remains the same

  simp at C,
  simp [sokostate.move],
  by_cases Cba : box ∈ avail, {
    simp [Cba], by_cases Cbb : box ∈ s.boxes, {
      simp [Cbb], by_cases Cb2a : box2 ∈ avail, {
        simp [Cb2a], by_cases Cb2b : box2 ∈ s.boxes,
        { simp [Cb2b], exact Hin, }, {
          simp [Cb2b],
          have C := C Cbb Cb2a Cb2b,
          cases not_or_distrib.mp C with C1 C2,
          have C2 := not_not.mp C2,
          rw boxint.mem.unfold, split,
            exact or.resolve_right (Hv.sk_comp_closed s.storekeeper Hsk d Cba) C1,
          split, {
            intros xy Hin, apply bset2d.mem_add_of_mem,
            apply bset2d.mem_remove_of_neq_mem,
            { intro contra, rw contra at Hin, exact C1 Hin, },
            { exact Hsub xy Hin },
          }, {
            intros xy Hin, cases bset2d.of_mem_add Hin with Heq Hin,
            { rw Heq, exact C2, },
            { exact Hsup xy (bset2d.mem_of_mem_remove Hin), },
          },
        },
      },
      { simp [Cb2a], exact Hin, },
    },
    { simp [Cbb], split,
      exact or.resolve_right
        (Hv.sk_comp_closed s.storekeeper Hsk d Cba)
        (mt (Hsub box) Cbb),
      exact and.intro Hsub Hsup,
    },
  },
  { simp [Cba], exact Hin, },
end
