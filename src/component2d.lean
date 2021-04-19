import data.list.func
import .list2d
import .boolset2d
import .component1d
import .direction

--         _                  _ _   _               
--    __ _| | __ _  ___  _ __(_) |_| |__  _ __ ___  
--   / _` | |/ _` |/ _ \| '__| | __| '_ \| '_ ` _ \ 
--  | (_| | | (_| | (_) | |  | | |_| | | | | | | | |
--   \__,_|_|\__, |\___/|_|  |_|\__|_| |_|_| |_| |_|
--           |___/                                  

def component_extend_rows (avail ini : bset2d) : bset2d
  := list.func.pointwise component1d avail ini
def component_extend_cols (avail ini : bset2d) : bset2d
  := list2d.transpose (component_extend_rows (list2d.transpose avail) (list2d.transpose ini))
def component_step (avail : bset2d) : bset2d → bset2d
  := (component_extend_cols avail) ∘ (component_extend_rows avail)
def comp_measure (avail ini : bset2d) : ℕ
  := avail.count - ini.count

def component2d_aux : ℕ → bset2d → bset2d → bset2d
| 0 _ cur := cur
| (b0+1) avail cur := let next := (component_step avail cur) in
  if comp_measure avail next < comp_measure avail cur
  then component2d_aux b0 avail next
  else cur

def component2d (avail ini : bset2d) : bset2d :=
  let ini_pure := list2d.pointwise2d band avail ini in
  component2d_aux (comp_measure avail ini_pure) avail ini_pure

--   _           _            _   _           
--  (_)_ __   __| |_   _  ___| |_(_)_   _____ 
--  | | '_ \ / _` | | | |/ __| __| \ \ / / _ \
--  | | | | | (_| | |_| | (__| |_| |\ V /  __/
--  |_|_| |_|\__,_|\__,_|\___|\__|_| \_/ \___|
--                                            

inductive in_component2d (avail ini : bset2d) : ℕ×ℕ → Prop
| triv (xy : ℕ×ℕ) (Ha : xy ∈ avail) (Hi : xy ∈ ini)
  : in_component2d xy
| move (d : direction) (xy : ℕ×ℕ) (Ha : xy ∈ avail)
  (Hc : in_component2d (d.shift xy))
  : in_component2d xy

theorem in_component2d_trans (avail ini ini2 : bset2d) :
  (∀ xy : ℕ×ℕ, xy ∈ avail → xy ∈ ini2
    → in_component2d avail ini xy) →
  ∀ xy : ℕ×ℕ, in_component2d avail ini2 xy → in_component2d avail ini xy :=
begin
  intros H1 xy H2, induction H2 with xy Ha Hi d xy Ha Hc IH,
  exact H1 xy Ha Hi,
  exact in_component2d.move d _ Ha IH,
end
theorem in_component2d_transpose : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  in_component2d avail.transpose ini.transpose xy →
  in_component2d avail ini (prod.swap xy) :=
begin
  introv H,
  induction H with xy Ha Hi d xy Ha Hc IH, {
    unfold has_mem.mem at Ha Hi,
    rw list2d.get2d_transpose at *,
    exact in_component2d.triv _ Ha Hi,
  }, {
    unfold has_mem.mem at Ha Hc,
    rw list2d.get2d_transpose at Ha,
    apply in_component2d.move d.transpose, exact Ha,
    simp [direction.transpose_shift], exact IH
  }
end
theorem in_component2d_subset_avail : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  in_component2d avail ini xy → xy ∈ avail :=
begin
  introv H, cases H with xy Ha Hi d xy Ha Hi,
  exact Ha, exact Ha,
end
theorem in_component2d_of_supset : ∀ (avail ini ini2 : bset2d),
  ini2 ⊆ ini →
  ∀ xy : ℕ×ℕ, in_component2d avail ini2 xy →
  in_component2d avail ini xy :=
begin
  introv Hsub Ha, refine in_component2d_trans avail ini ini2 _ xy Ha,
  clear Ha xy, introv Ha Hi,
  exact in_component2d.triv xy Ha (Hsub xy Hi),
end

--             _                 _                           
--    _____  _| |_ ___ _ __   __| |    _ __ _____      _____ 
--   / _ \ \/ / __/ _ \ '_ \ / _` |   | '__/ _ \ \ /\ / / __|
--  |  __/>  <| ||  __/ | | | (_| |   | | | (_) \ V  V /\__ \
--   \___/_/\_\\__\___|_| |_|\__,_|___|_|  \___/ \_/\_/ |___/
--                               |_____|                     

theorem component_extend_rows_valid : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  xy ∈ (component_extend_rows avail ini) →
  in_component2d avail ini xy
:=
begin
  unfold component_extend_rows, introv H,
  cases xy with x y, unfold has_mem.mem at H, unfold list2d.get2d at H,
  rw list.func.get_pointwise at H,
  have H1 := component1d_valid _ _ _ H, clear H,
  induction H1 with x Ha Hi x Ha Hc IH x Ha Hc IH,
  { apply in_component2d.triv (x,y), exact Ha, exact Hi, },
  { apply in_component2d.move direction.right, exact Ha, exact IH, },
  { apply in_component2d.move direction.left, exact Ha, exact IH, },
  simp [default, component1d],
end
theorem component_extend_rows_subset_avail
  : ∀ (avail ini : bset2d), (component_extend_rows avail ini) ⊆ avail :=
begin
  intros avail ini xy, cases xy with x y,
  unfold has_mem.mem, unfold list2d.get2d,
  unfold component_extend_rows, rw list.func.get_pointwise,
  exact component1d_subset_avail _ _ _,
  simp! [default, component1d],
end
theorem component_extend_rows_supset
  : ∀ (avail ini : bset2d), ini ⊆ avail →
  ini ⊆ (component_extend_rows avail ini) :=
begin
  intros avail ini H xy, cases xy with x y,
  unfold has_mem.mem, unfold list2d.get2d,
  unfold component_extend_rows, rw list.func.get_pointwise,
  intro H2, exact component1d_supset _ _ _ (H (x,y) H2) H2,
  simp! [default, component1d],
end

theorem component_extend_rows_works {avail ini : bset2d} {xy : ℕ×ℕ}
  : ∀ (d : direction),
  xy ∈ avail → (d.shift xy) ∈ avail → (d.shift xy) ∈ ini →
  (d = direction.left ∨ d = direction.right) →
  xy ∈ (component_extend_rows avail ini) :=
begin
  introv Ha Hda Hdi Hd, cases xy with x y,
  unfold has_mem.mem, unfold list2d.get2d,
  unfold component_extend_rows, rw list.func.get_pointwise,
  cases Hd, {
    simp [Hd, direction.shift, list2d.get2d] at *,
    cases x, { exact component1d_supset _ _ _ Ha Hdi, },
    simp at Hda Hdi, rw (component1d_succ_eq _ _ x Hda Ha),
    exact component1d_supset _ _ _ Hda Hdi,
  }, {
    simp [Hd, direction.shift, list2d.get2d] at *,
    rw ←(component1d_succ_eq _ _ x Ha Hda),
    exact component1d_supset _ _ _ Hda Hdi,
  },
  simp! [default, component1d],
end

--             _                 _              _     
--    _____  _| |_ ___ _ __   __| |    ___ ___ | |___ 
--   / _ \ \/ / __/ _ \ '_ \ / _` |   / __/ _ \| / __|
--  |  __/>  <| ||  __/ | | | (_| |  | (_| (_) | \__ \
--   \___/_/\_\\__\___|_| |_|\__,_|___\___\___/|_|___/
--                               |_____|              


theorem component_extend_cols_valid : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  xy ∈ (component_extend_cols avail ini) →
  in_component2d avail ini xy
:=
begin
  unfold component_extend_cols, unfold has_mem.mem, introv,
  rw list2d.get2d_transpose, introv H,
  have H := component_extend_rows_valid _ _ _ H,
  have H := in_component2d_transpose _ _ _ H,
  simp at H, exact H,
end
theorem component_extend_cols_subset_avail
  : ∀ (avail ini : bset2d), (component_extend_cols avail ini) ⊆ avail :=
begin
  intros avail ini xy H, unfold has_mem.mem at H, 
  unfold component_extend_cols at H, rw list2d.get2d_transpose at H,
  have H := component_extend_rows_subset_avail _ _ _ H,
  unfold has_mem.mem at H,
  rw list2d.get2d_transpose at H, simp at H, exact H,
end
theorem component_extend_cols_supset
  : ∀ (avail ini : bset2d), ini ⊆ avail →
  ini ⊆ (component_extend_cols avail ini) :=
begin
  intros avail ini H1 xy H2, unfold component_extend_cols,
  unfold has_mem.mem,
  rw list2d.get2d_transpose, apply component_extend_rows_supset, {
    intro xy, unfold has_mem.mem,
    simp [list2d.get2d_transpose], apply H1,
  },
  unfold has_mem.mem,
  rw list2d.get2d_transpose, simp, exact H2,
end

theorem component_extend_cols_works {avail ini : bset2d} {xy : ℕ×ℕ}
  : ∀ (d : direction),
  xy ∈ avail → (d.shift xy) ∈ avail → (d.shift xy) ∈ ini →
  (d = direction.up ∨ d = direction.down) →
  xy ∈ (component_extend_cols avail ini) :=
begin
  introv Ha Hda Hdi Hd,
  unfold component_extend_cols, unfold has_mem.mem, cases xy with x y, simp,
  apply component_extend_rows_works d.transpose,
  { simp [has_mem.mem], exact Ha },
  { simp [has_mem.mem, direction.transpose_shift], exact Hda },
  { simp [has_mem.mem, direction.transpose_shift], exact Hdi },
  { cases Hd, rw Hd, left, refl, rw Hd, right, refl, },
end

--                                    _             
--    ___ ___  _ __ ___  _ __     ___| |_ ___ _ __  
--   / __/ _ \| '_ ` _ \| '_ \   / __| __/ _ \ '_ \ 
--  | (_| (_) | | | | | | |_) |  \__ \ ||  __/ |_) |
--   \___\___/|_| |_| |_| .__/___|___/\__\___| .__/ 
--                      |_| |_____|          |_|    

theorem component_step_valid : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  xy ∈ (component_step avail ini) →
  in_component2d avail ini xy
:=
begin
  unfold component_step, simp, introv H,
  apply in_component2d_trans _ _ (component_extend_rows avail ini), {
    clear H xy, intros xy H1 H2,
    exact component_extend_rows_valid _ _ _ H2,
  },
  { exact component_extend_cols_valid _ _ _ H, },
end
theorem component_step_subset_avail
  : ∀ (avail ini : bset2d), (component_step avail ini) ⊆ avail :=
begin
  intros, unfold component_step, simp,
  apply component_extend_cols_subset_avail,
end
theorem component_step_supset
  : ∀ (avail ini : bset2d), ini ⊆ avail →
  ini ⊆ (component_step avail ini) :=
begin
  introv H, unfold component_step, simp,
  apply @bset2d.subset.trans _ (component_extend_rows avail ini),
  exact component_extend_rows_supset _ _ H,
  apply component_extend_cols_supset,
  exact component_extend_rows_subset_avail _ _,
end

theorem component_step_complete_of_nlt_measure
  : ∀ (avail ini : bset2d),
  ini ⊆ avail →
  (¬ comp_measure avail (component_step avail ini) < comp_measure avail ini) →
  ∀ xy : ℕ×ℕ, in_component2d avail ini xy →
  xy ∈ ini
:=
begin
  introv Hia_sub Hm_nlt Hin,
  have Hsub : (component_step avail ini) ⊆ ini, {
    clear Hin xy,
    have Hm_ge : comp_measure avail (component_step avail ini) ≥ comp_measure avail ini
      := not_lt.mp Hm_nlt, clear Hm_nlt,
    unfold comp_measure at Hm_ge,
    have Hca_le : (component_step avail ini).count ≤ avail.count
      := bset2d.count_le_of_subset (component_step avail ini) avail
        (component_step_subset_avail avail _),
    have Hci_le : (component_step avail ini).count ≤ ini.count
      := (nat.sub_le_sub_left_iff Hca_le).mp Hm_ge,
    have Hic_sub : ini ⊆ (component_step avail ini)
      := component_step_supset avail ini Hia_sub,
    have Hic_le : ini.count ≤ (component_step avail ini).count
      := bset2d.count_le_of_subset ini _ Hic_sub,
    have Hic_eq : ini.count = (component_step avail ini).count
      := le_antisymm Hic_le Hci_le,
    exact bset2d.subset_eq_of_count_eq ini (component_step avail ini) Hic_sub Hic_eq,
  },
  induction Hin with xy Ha Hi d xy Ha Hc IH, { exact Hi, }, {
  have Had : (d.shift xy) ∈ avail
    := in_component2d_subset_avail avail ini (d.shift xy) Hc,
  apply Hsub,
  have Hlr : xy ∈ (component_extend_rows avail ini)
    → xy ∈ (component_step avail ini)
    := component_extend_cols_supset avail _
      (component_extend_rows_subset_avail avail ini) xy,
  have Hud : (d.shift xy) ∈ (component_extend_rows avail ini)
    := component_extend_rows_supset avail _ Hia_sub (d.shift xy) IH,
  unfold component_step, simp,
  cases d,
  { exact component_extend_cols_works direction.up Ha Had Hud
      (or.intro_left _ rfl), },
  { exact component_extend_cols_works direction.down Ha Had Hud
      (or.intro_right _ rfl), },
  { exact Hlr (component_extend_rows_works direction.left Ha Had IH
      (or.intro_left _ rfl)), },
  { exact Hlr (component_extend_rows_works direction.right Ha Had IH
      (or.intro_right _ rfl)), },
  },
end

--                                                
--    ___ ___  _ __ ___  _ __     __ _ _   ___  __
--   / __/ _ \| '_ ` _ \| '_ \   / _` | | | \ \/ /
--  | (_| (_) | | | | | | |_) | | (_| | |_| |>  < 
--   \___\___/|_| |_| |_| .__/___\__,_|\__,_/_/\_\
--                      |_| |_____|               


theorem component2d_aux_valid : ∀ (b : ℕ) (avail ini : bset2d) (xy : ℕ×ℕ),
  ini ⊆ avail →
  xy ∈ (component2d_aux b avail ini) →
  in_component2d avail ini xy
:=
begin
  intro b, induction b with b IH, {
    introv Hsub H,
    unfold component2d_aux at H,
    exact in_component2d.triv xy (Hsub xy H) H,
  }, {
    introv Hsub H,
    unfold component2d_aux at H, simp at H,
    by_cases Hcond : (comp_measure avail (component_step avail ini) < comp_measure avail ini),
    { rw if_pos Hcond at H, 
      apply in_component2d_trans _ _ (component_step avail ini),
      { clear H xy, introv Ha Hc, apply component_step_valid, exact Hc, },
      { apply IH _ _ _ _ H, apply component_step_subset_avail, },
    }, {
      rw if_neg Hcond at H,
      exact in_component2d.triv xy (Hsub xy H) H,
    }
  }
end

theorem component2d_aux_complete : ∀ (b : ℕ) (avail ini : bset2d) (xy : ℕ×ℕ),
  ini ⊆ avail →
  comp_measure avail ini ≤ b →
  in_component2d avail ini xy →
  xy ∈ (component2d_aux b avail ini)
:=
begin
  intro b, induction b with b IH, {
    introv Hsub Hm Hin,
    unfold component2d_aux,
    refine component_step_complete_of_nlt_measure avail ini Hsub _ xy Hin,
    { simp at Hm, rw Hm, apply nat.not_lt_zero, },
  }, {
    introv Hsub Hm Hin,
    unfold component2d_aux, simp,
    by_cases Hcond
      : (comp_measure avail (component_step avail ini) < comp_measure avail ini), {
      rw if_pos Hcond,
      apply IH,
      { apply component_step_subset_avail, },
      { exact nat.succ_le_succ_iff.mp (le_trans (nat.succ_le_iff.mpr Hcond) Hm) },
      { refine in_component2d_of_supset avail _ ini _ xy Hin,
        exact component_step_supset avail ini Hsub, },
    }, {
      rw if_neg Hcond,
      exact component_step_complete_of_nlt_measure avail ini Hsub Hcond xy Hin,
    },
  },
end

--                                                    _   ____     _ 
--    ___ ___  _ __ ___  _ __   ___  _ __   ___ _ __ | |_|___ \ __| |
--   / __/ _ \| '_ ` _ \| '_ \ / _ \| '_ \ / _ \ '_ \| __| __) / _` |
--  | (_| (_) | | | | | | |_) | (_) | | | |  __/ | | | |_ / __/ (_| |
--   \___\___/|_| |_| |_| .__/ \___/|_| |_|\___|_| |_|\__|_____\__,_|
--                      |_|                                          

theorem component2d_valid : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  xy ∈ (component2d avail ini) →
  in_component2d avail ini xy
:=
begin
  unfold component2d, simp, introv H, 
  apply in_component2d_trans _ _ (list2d.pointwise2d band avail ini),
  clear H xy, introv Ha Hri, {
    unfold has_mem.mem at Hri,
    rw list2d.get2d_pointwise at Hri, simp at Hri, cases Hri with Ha Hi,
    apply in_component2d.triv xy Ha, exact Hi,
    simp!,
  }, {
    apply component2d_aux_valid _ _ _ _ _ H, {
      clear H, intro xy, intro H,
      unfold has_mem.mem at H,
      rw list2d.get2d_pointwise at H, simp at H, cases H with Ha Hi,
      exact Ha,
      simp!,
    },
  },
end
theorem component2d_complete : ∀ (avail ini : bset2d) (xy : ℕ×ℕ),
  in_component2d avail ini xy →
  xy ∈ (component2d avail ini)
:=
begin
  introv Hin, unfold component2d, simp,
  apply component2d_aux_complete _ avail _ xy, {
    clear Hin xy, intros xy H,
    unfold has_mem.mem at H,
    simp [list2d.get2d_pointwise] at H,
    exact H.elim_left,
  }, exact le_refl _, {
    refine in_component2d_trans avail _ ini _ xy Hin,
    intros xy Ha Hi,
    apply in_component2d.triv xy Ha,
    simp [has_mem.mem, list2d.get2d_pointwise], exact and.intro Ha Hi,
  },
end
theorem component2d_op_closed : ∀ {avail ini : bset2d} {xy : ℕ×ℕ} {d : direction},
  d.shift xy ∈ (component2d avail ini) →
  xy ∈ avail →
  xy ∈ (component2d avail ini) :=
begin
  introv Hc Ha, apply component2d_complete,
  have Hc := component2d_valid avail ini (d.shift xy) Hc,
  exact in_component2d.move d xy Ha Hc,
end
theorem component2d_closed : ∀ {avail ini : bset2d} {xy : ℕ×ℕ} {d : direction},
  xy ∈ (component2d avail ini) →
  d.shift xy ∈ avail →
  d.shift xy ∈ (component2d avail ini) :=
begin
  introv Hc Ha, cases direction.opposite_shift d xy with Heq Hrev,
  { rw Heq, exact Hc, },
  rw ←Hrev at Hc, exact component2d_op_closed Hc Ha,
end
theorem component2d_subset_avail : ∀ {avail ini : bset2d},
  (component2d avail ini) ⊆ avail :=
λ avail ini xy Hin, in_component2d_subset_avail _ _ _ (component2d_valid _ _ _ Hin)

theorem component2d_supset : ∀ {avail ini : bset2d},
  ini ⊆ avail → ini ⊆ (component2d avail ini) :=
assume avail ini Hsub xy Hin,
  component2d_complete _ _ _ (in_component2d.triv xy (Hsub xy Hin) Hin)
