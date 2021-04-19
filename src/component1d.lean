import data.list.func
import .helpers
import .boolset2d

def component1d : bset1d → bset1d → bset1d
| [] _ := []
| (ha::ta) ini := let hi := ini.head, ti := ini.tail in
  let hha := ti.head in
  let tcomp := component1d ta ((hha||(hi&&ha))::ti.tail) in
  (ha && (hi || tcomp.head))::tcomp

inductive in_component1d (avail ini : bset1d) : ℕ → Prop
| triv (n : ℕ) (Ha : n ∈ avail) (Hi : n ∈ ini)
  : in_component1d n
| move_fw (n : ℕ) (Ha : n ∈ avail) (Hc : in_component1d n.succ)
  : in_component1d n
| move_bw (n : ℕ) (Ha : n ∈ avail) (Hc : in_component1d n.pred)
  : in_component1d n

theorem component1d_ini_split : ∀ (avail ini : bset1d),
  component1d avail (ini.head::ini.tail) = component1d avail ini :=
begin
  intros, cases avail, simp! [component1d],
  simp! [component1d, list.head],
end
theorem component1d_avail_cons_ff : ∀ (avail ini : bset1d),
  component1d (ff::avail) ini = ff::(component1d avail (ini.tail)) :=
begin
  intros, unfold component1d, simp [component1d_ini_split],
end

theorem in_component1d_of_in_cons : ∀ (b : bool) (avail ini : bset1d) (n : ℕ),
  (in_component1d avail (ini.tail) n) → in_component1d (b::avail) ini n.succ :=
begin
  introv H, induction H with n Ha Hi n Ha Hc IH n Ha Hc IH,
  { apply in_component1d.triv,
    all_goals { unfold has_mem.mem at *, rw get_succ, assumption } },
  { apply in_component1d.move_fw,
    all_goals { assumption <|> exact IH }, },
  { cases n, exact IH,
    apply in_component1d.move_bw,
    all_goals { assumption <|> exact IH },
  },
end

theorem in_component1d_trans (avail ini ini2 : bset1d) :
  (∀ n, n ∈ avail → n ∈ ini2
    → in_component1d avail ini n) →
  ∀ n, in_component1d avail ini2 n → in_component1d avail ini n :=
begin
  intros H1 n H2, induction H2 with n Ha Hi n Ha Hc IH n Ha Hc IH,
  exact H1 n Ha Hi,
  exact in_component1d.move_fw _ Ha IH,
  exact in_component1d.move_bw _ Ha IH,
end

theorem component1d_valid : ∀ (avail ini : bset1d) (n : ℕ),
  n ∈ (component1d avail ini) → in_component1d avail ini n :=
begin
  intro avail, induction avail, {
    introv H, unfold component1d at H,
    simp [has_mem.mem] at H, contradiction,
  }, {
    introv H, cases avail_hd, {
      cases n,
      simp at H, contradiction,
      apply in_component1d_of_in_cons,
      simp [component1d_avail_cons_ff] at H,
      exact avail_ih _ _ H,
    }, {
      rw ←component1d_ini_split at H, unfold component1d at H,
      simp [list.head, list.tail] at H,
      cases Eh : list.head ini, {
        simp [Eh, component1d_ini_split] at H,
        cases Ech : (component1d avail_tl ini.tail).head,
        { rw [Ech] at H,
          cases n, simp at H, contradiction,
          simp [has_mem.mem] at H,
          apply in_component1d_of_in_cons,
          exact avail_ih _ n H,
        }, {
          rw [Ech] at H,
          cases n, {
            apply in_component1d.move_fw, simp [has_mem.mem],
            apply in_component1d_of_in_cons,
            apply avail_ih, simp [has_mem.mem, get_0_head], exact Ech,
          }, {
            apply in_component1d_of_in_cons,
            apply avail_ih, exact H,
          }
        }
      }, {
        rw Eh at H, simp at H,
        cases n, {
          apply in_component1d.triv, simp! [has_mem.mem],
          unfold has_mem.mem, rw get_0_head, exact Eh,
        }, {
          simp [has_mem.mem] at H, specialize avail_ih _ _ H,
          apply in_component1d_trans _ _ (tt::tt:: ini.tail.tail), {
            clear avail_ih H n, intros n H1 H2,
            cases n, { apply in_component1d.triv _ H1,
              unfold has_mem.mem, rw get_0_head, exact Eh, },
            cases n, {
              apply in_component1d.move_bw _ H1,
              apply in_component1d.triv,
              simp! [has_mem.mem],
              simp! [has_mem.mem, Eh, get_0_head],
            }, {
              apply in_component1d.triv,
              { simp [has_mem.mem, get_succ], simp [has_mem.mem, get_succ] at H1, exact H1, },
              { simp [has_mem.mem, get_succ], exact H2, },
            }
          },
          exact in_component1d_of_in_cons _ _ _ _ avail_ih,
        }
      }
    }
  },
end

theorem component1d_subset_avail : ∀ (avail ini : bset1d) (n : ℕ),
  list.func.get n (component1d avail ini) = tt → list.func.get n avail = tt :=
begin
  intro avail, induction avail,
  { intros ini n H, simp [component1d] at H, contradiction, },
  intros ini n H, cases n, {
    simp [component1d] at H, cases H with H1 H2,
    simp, exact H1,
  }, {
    simp, simp [component1d] at H, exact avail_ih _ _ H,
  }
end
theorem component1d_supset : ∀ (avail ini : bset1d) (n : ℕ),
  list.func.get n avail = tt → list.func.get n ini = tt
  → list.func.get n (component1d avail ini) = tt :=
begin
  intro avail, induction avail,
  { introv H1 H2, intros, simp at H1, contradiction, },
  introv H1 H2,
  cases n, {
    simp at H1, rw H1, clear H1,
    simp [get_0_head] at H2,
    simp [component1d], left, exact H2,
  }, {
    simp at H1,
    simp [get_succ] at H2,
    simp [component1d], apply avail_ih, {
      exact H1,
    }, {
      cases n, simp, left, 
      simp [get_0_head] at H2, exact H2,
      simp [get_succ] at H2, simp, exact H2,
    }
  }
end
theorem component1d_succ_eq : ∀ (avail ini : bset1d) (n : ℕ),
  list.func.get n avail = tt → list.func.get n.succ avail = tt →
  list.func.get n.succ (component1d avail ini) = 
  list.func.get n (component1d avail ini) :=
begin
  intro avail, induction avail, {
    introv H1 H2, simp at H1, contradiction,
  }, {
    introv H1 H2, cases n, {
      simp at H1, simp [get_0_head] at H2,
      rewrite H1, clear H1, simp,
      unfold component1d,
      cases ini.head, simp,
      apply get_0_head,
      simp, cases avail_tl, { simp at H2, contradiction, },
      simp at H2, rewrite H2, unfold component1d, simp,
    },
    unfold component1d, exact avail_ih _ _ H1 H2,
  }
end

theorem component1d_complete : ∀ (avail ini : bset1d) (n : ℕ),
  in_component1d avail ini n → list.func.get n (component1d avail ini) = tt :=
begin
  introv H, induction H with n Ha Hi n Ha Hc IH n Ha Hc IH,
  { apply component1d_supset, exact Ha, exact Hi, },
  { rw ←component1d_succ_eq, exact IH, exact Ha, 
    exact component1d_subset_avail avail ini n.succ IH, },
  { cases n with n, exact IH, simp at IH,
    rw component1d_succ_eq, exact IH,
    exact component1d_subset_avail avail ini n IH,
    exact Ha, },
end
