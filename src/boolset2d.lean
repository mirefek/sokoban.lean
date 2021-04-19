import data.list.func
import .helpers
import .list2d
import .find_indexes2d

def bset1d := list bool
def bset2d := list2d bool

instance : inhabited bset1d := ⟨[]⟩
instance : inhabited bset2d := ⟨[]⟩

instance : has_mem ℕ bset1d :=
⟨λ n l, list.func.get n l = tt⟩
instance : has_mem (ℕ×ℕ) bset2d :=
⟨λ xy l, list2d.get2d xy l = tt⟩
lemma bset1d.has_mem.unfold {n : ℕ} {l : bset1d}
  : n ∈ l = (list.func.get n l = tt) := rfl
lemma bset2d.has_mem.unfold {xy : ℕ×ℕ} {l : bset2d}
  : xy ∈ l = (list2d.get2d xy l = tt) := rfl

instance : has_sdiff bset2d
:= ⟨list2d.pointwise2d (λ a b, (cond b ff a))⟩
instance : has_inter bset2d
:= ⟨list2d.pointwise2d band⟩
instance : has_union bset2d
:= ⟨list2d.pointwise2d bor⟩

def pic_str1d (l : bset1d) : string :=
  string.push (list.as_string (l.map (λb, cond b '*' '.'))) '\n'
def pic_str2d (l : bset2d) : string :=
  string.join (l.map pic_str1d)
instance : has_repr bset1d := ⟨pic_str1d⟩
instance : has_repr bset2d := ⟨pic_str2d⟩

--             _              _   
--   ___ _   _| |__  ___  ___| |_ 
--  / __| | | | '_ \/ __|/ _ \ __|
--  \__ \ |_| | |_) \__ \  __/ |_ 
--  |___/\__,_|_.__/|___/\___|\__|
--                                

def bset1d.subset (l1 : bset1d) (l2 : bset1d) : Prop
  := ∀ x : ℕ, x ∈ l1 → x ∈ l2
def bset2d.subset (l1 : bset2d) (l2 : bset2d) : Prop
  := ∀ xy : ℕ×ℕ, xy ∈ l1 → xy ∈ l2
instance : has_subset bset1d := ⟨bset1d.subset⟩
instance : has_subset bset2d := ⟨bset2d.subset⟩

def bset2d.disjoint (l1 : bset2d) (l2 : bset2d) : Prop
  := ∀ xy : ℕ×ℕ, xy ∈ l1 → xy ∈ l2 → false

theorem bset2d.subset.refl : ∀ {l1 : bset2d}, l1 ⊆ l1
:= assume l1 xy H, H
theorem bset2d.subset.trans : ∀ {l1 l2 l3 : bset2d},
  l1 ⊆ l2 → l2 ⊆ l3 → l1 ⊆ l3
:= assume l1 l2 l3 H12 H23 xy H1, H23 xy (H12 xy H1)

theorem bset2d.subset_of_equiv : ∀ {l1 l2 : bset2d},
  list2d.equiv l1 l2 → l1 ⊆ l2 :=
begin
  intros l1 l2 Heq xy Hget,
  unfold has_mem.mem at Hget, 
  rw Heq xy at Hget, exact Hget,
end

--                         _   _             
--    ___ ___  _   _ _ __ | |_(_)_ __   __ _ 
--   / __/ _ \| | | | '_ \| __| | '_ \ / _` |
--  | (_| (_) | |_| | | | | |_| | | | | (_| |
--   \___\___/ \__,_|_| |_|\__|_|_| |_|\__, |
--                                     |___/ 

def bset1d.count (l : bset1d) : ℕ := list.sum (list.map bool.to_nat l)
def bset2d.count (l : bset2d) : ℕ := list.sum (list.map bset1d.count l)

@[simp] theorem bset1d.count_nil : bset1d.count [] = 0 := rfl
@[simp] theorem bset2d.count_nil : bset2d.count [] = 0 := rfl
@[simp] theorem bset1d.count_cons : ∀ (h : bool) (t : bset1d),
  bset1d.count (h::t) = (bool.to_nat h) + t.count := by simp [bset1d.count]
@[simp] theorem bset2d.count_cons : ∀ (h : bset1d) (t : bset2d),
  bset2d.count (h::t) = h.count + t.count := by simp [bset2d.count]

--                         _                       _              _   
--    ___ ___  _   _ _ __ | |_     _     ___ _   _| |__  ___  ___| |_ 
--   / __/ _ \| | | | '_ \| __|  _| |_  / __| | | | '_ \/ __|/ _ \ __|
--  | (_| (_) | |_| | | | | |_  |_   _| \__ \ |_| | |_) \__ \  __/ |_ 
--   \___\___/ \__,_|_| |_|\__|   |_|   |___/\__,_|_.__/|___/\___|\__|
--                                                                    

theorem bool_to_nat_le {b1 b2 : bool} :
  (b1.to_nat ≤ b2.to_nat) ↔ (b1 = tt → b2 = tt) :=
begin
  intros, split, {
    intro H, cases b1, simp,
    cases b2, simp [bool.to_nat] at H, contradiction,
    simp,
  }, {
    intro H, cases b1, simp [bool.to_nat],
    cases b2, simp at H, contradiction,
    apply le_rfl,
  }
end

theorem bset1d.subset_cons : ∀ (h1 h2 : bool) (t1 t2 : bset1d),
  bset1d.subset (h1::t1) (h2::t2) = (h1.to_nat ≤ h2.to_nat ∧ t1 ⊆ t2) :=
begin
  intros, apply propext, split, {
    intro H, split, exact bool_to_nat_le.2 (H 0),
    intro n, exact H n.succ
  }, {
    intro H, cases H with H1 H2,
    intro n, cases n, exact bool_to_nat_le.1 H1,
    exact H2 n,
  }
end
theorem bset2d.subset_cons : ∀ (h1 h2 : bset1d) (t1 t2 : bset2d),
  bset2d.subset (h1::t1) (h2::t2) = (h1 ⊆ h2 ∧ t1 ⊆ t2) :=
begin
  intros, apply propext, split, {
    intro H, split, intro x, exact H (x,0),
    intro xy, cases xy with x y, exact H (x,y+1)
  }, {
    intro H, cases H with H1 H2,
    intro xy, cases xy with x y, cases y, apply H1,
    exact H2 (x, y),
  }
end

theorem bset1d.count_0_of_subset_nil : ∀ l : bset1d,
  bset1d.subset l list.nil → l.count = 0
| [] := by simp
| (h::t) := begin
  intro H, simp, split, {
    have := H 0, simp [has_mem.mem] at this,
    rw bool_eq_false this, refl,
  }, {
    apply bset1d.count_0_of_subset_nil,
    intros n H2, specialize H (n+1), simp [has_mem.mem] at H, contradiction,
  }
end
theorem bset2d.count_0_of_subset_nil : ∀ l : bset2d,
  bset2d.subset l list.nil → l.count = 0
| [] := by simp
| (h::t) := begin
  intro H, simp, split, {
    apply bset1d.count_0_of_subset_nil,
    intro x, exact H (x,0),
  }, {
    apply bset2d.count_0_of_subset_nil,
    intros xy H2, cases xy with x y,
    specialize H (x,y+1), simp [has_mem.mem] at H, contradiction,
  }
end

theorem bset1d.count_le_of_subset : ∀ l1 l2 : bset1d,
  l1 ⊆ l2 → l1.count ≤ l2.count
| [] _ := by simp
| _ [] := begin
  intros H, have H := bset1d.count_0_of_subset_nil _ H, rewrite H,
  apply zero_le,
end
| (h1::t1) (h2::t2) := begin
  simp [has_subset.subset, bset1d.subset_cons], intros Hh Ht, apply add_le_add,
  exact Hh,
  exact bset1d.count_le_of_subset _ _ Ht,
end

theorem bset2d.count_le_of_subset : ∀ l1 l2 : bset2d,
  l1 ⊆ l2 → l1.count ≤ l2.count
| [] _ := by simp
| _ [] := begin
  intros H, have H := bset2d.count_0_of_subset_nil _ H, rewrite H,
  apply zero_le,
end
| (h1::t1) (h2::t2) := begin
  simp [has_subset.subset, bset2d.subset_cons], intros Hh Ht, apply add_le_add,
  exact bset1d.count_le_of_subset _ _ Hh,
  exact bset2d.count_le_of_subset _ _ Ht,
end

lemma leq_sum_equal {a b c d : ℕ} :
  a ≤ b → c ≤ d → a+c = b+d → a=b ∧ c=d := by omega

theorem bset1d.subset_nil_of_count_0 : ∀ l : bset1d,
  l.count = 0 → bset1d.subset l list.nil
| [] := λ _ _ H, H
| (h::t) := begin
  simp, intros Hh Ht n, cases n, {
    cases h, intro H, simp at H, contradiction,
    simp [bool.to_nat] at Hh, contradiction,
  }, {
    have := bset1d.subset_nil_of_count_0 t Ht n,
    simp [has_mem.mem], simp [has_mem.mem] at this, exact this,
  }
end
theorem bset2d.subset_nil_of_count_0 : ∀ l : bset2d,
  l.count = 0 → bset2d.subset l list.nil
| [] := λ _ _ H, H
| (h::t) := begin
  simp, intros Hh Ht xy, cases xy with x y, cases y, {
    exact bset1d.subset_nil_of_count_0 h Hh x,
  }, {
    have := bset2d.subset_nil_of_count_0 t Ht (x,y),
    simp [has_mem.mem], simp [has_mem.mem] at this, exact this,
  }
end

theorem bset1d.subset_eq_of_count_eq : ∀ l1 l2 : bset1d,
  l1 ⊆ l2 → l1.count = l2.count → l2 ⊆ l1
| _ [] := begin simp [has_mem.mem, has_subset.subset, bset1d.subset], end
| [] l2 := begin
  intros Hh Hc, simp at Hc,
  apply bset1d.subset_nil_of_count_0 l2 (eq.symm Hc),
end
| (h1::t1) (h2::t2) := begin
  simp [has_subset.subset, bset1d.subset_cons], intros Hh Ht Hc,
  have Ht_le := bset1d.count_le_of_subset t1 t2 Ht,
  cases leq_sum_equal Hh Ht_le Hc with Eh Et,
  split, simp! [Eh],
  exact bset1d.subset_eq_of_count_eq t1 t2 Ht Et,
end

theorem bset2d.subset_eq_of_count_eq : ∀ l1 l2 : bset2d,
  l1 ⊆ l2 → l1.count = l2.count → l2 ⊆ l1
| _ [] := by simp [has_mem.mem, has_subset.subset, bset2d.subset]
| [] l2 := begin
  intros Hh Hc, simp at Hc,
  apply bset2d.subset_nil_of_count_0 l2 (eq.symm Hc),
end
| (h1::t1) (h2::t2) := begin
  simp [has_subset.subset, bset1d.subset_cons, bset2d.subset_cons],
  intros Hh Ht Hc,
  have Hh_le := bset1d.count_le_of_subset h1 h2 Hh,
  have Ht_le := bset2d.count_le_of_subset t1 t2 Ht,
  cases leq_sum_equal Hh_le Ht_le Hc with Eh Et,
  split, apply bset1d.subset_eq_of_count_eq h1 h2 Hh Eh,
  exact bset2d.subset_eq_of_count_eq t1 t2 Ht Et,
end

--             _     _                                             
--    __ _  __| | __| |    _     _ __ ___ _ __ ___   _____   _____ 
--   / _` |/ _` |/ _` |  _| |_  | '__/ _ \ '_ ` _ \ / _ \ \ / / _ \
--  | (_| | (_| | (_| | |_   _| | | |  __/ | | | | | (_) \ V /  __/
--   \__,_|\__,_|\__,_|   |_|   |_|  \___|_| |_| |_|\___/ \_/ \___|
--                                                                 

def bset2d.add (xy : ℕ×ℕ) (l : bset2d) : bset2d := list2d.set2d tt l xy
def bset2d.remove (xy : ℕ×ℕ) (l : bset2d) : bset2d := list2d.set2d ff l xy

lemma bset2d.mem_add {xy : ℕ×ℕ} {l : bset2d}
  : xy ∈ (l.add xy) := list2d.get2d_set2d
lemma bset2d.mem_add_of_mem {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∈ l → xy ∈ (l.add xy') := begin
  assume H, by_cases C : xy = xy', rw C, exact list2d.get2d_set2d,
  exact eq.trans (list2d.get2d_set2d_eq_of_ne C) H,
end
lemma bset2d.nmem_add_of_neq_nmem {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ≠ xy' → xy ∉ l → xy ∉ (l.add xy')
:= λ Hn Hl Hadd, Hl (eq.trans (list2d.get2d_set2d_eq_of_ne Hn).symm Hadd)
lemma bset2d.nmem_remove {xy : ℕ×ℕ} {l : bset2d}
  : xy ∉ (l.remove xy)
:= by simp [has_mem.mem, bset2d.remove, list2d.get2d_set2d]
lemma bset2d.nmem_remove_of_nmem {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∉ l → xy ∉ (l.remove xy') := begin
  assume H, by_cases C : xy = xy', rw C, exact bset2d.nmem_remove,
  assume Hrem, exact H (eq.trans (list2d.get2d_set2d_eq_of_ne C).symm Hrem),
end
lemma bset2d.mem_remove_of_neq_mem {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ≠ xy' → xy ∈ l → xy ∈ (l.remove xy')
:= λ Hn Hl, eq.trans (list2d.get2d_set2d_eq_of_ne Hn) Hl

lemma bset2d.of_mem_add {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∈ (l.add xy') → xy = xy' ∨ xy ∈ l := begin
  intro H, by_cases C : xy = xy', left, exact C,
  right, by_contradiction Hnl,
  exact bset2d.nmem_add_of_neq_nmem C Hnl H,
end
lemma bset2d.nmem_of_nmem_add {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∉ (l.add xy') → xy ∉ l :=
begin
  intros Hnadd, by_contradiction Hl,
  exact Hnadd (bset2d.mem_add_of_mem Hl),
end
lemma bset2d.neq_of_nmem_add {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∉ (l.add xy') → xy ≠ xy' :=
begin
  intros Hnadd Heq, rw Heq at Hnadd,
  exact Hnadd (bset2d.mem_add),
end
lemma bset2d.of_nmem_remove {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∉ (l.remove xy') → xy = xy' ∨ xy ∉ l := begin
  intro H, by_cases C : xy = xy', left, exact C,
  right, by_contradiction Hl,
  refine H (bset2d.mem_remove_of_neq_mem _ Hl),
  assume Cn, exact C Cn,
end
lemma bset2d.mem_of_mem_remove {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∈ (l.remove xy') → xy ∈ l := begin
  intro Hrem, by_contradiction Hnl,
  exact bset2d.nmem_remove_of_nmem Hnl Hrem,
end
lemma bset2d.neq_of_mem_remove {xy xy' : ℕ×ℕ} {l : bset2d}
  : xy ∈ (l.remove xy') → xy ≠ xy' := begin
  intros Hrem Heq, rw Heq at Hrem,
  exact bset2d.nmem_remove Hrem,
end
lemma bset2d.subset_add_same {l1 l2 : bset2d} {xy : ℕ×ℕ}
  : l1 ⊆ l2 → l1.add xy ⊆ l2.add xy
:= begin
  intros Hsub xy' Hin, cases bset2d.of_mem_add Hin,
  rw h, exact bset2d.mem_add,
  apply bset2d.mem_add_of_mem, exact Hsub xy' h,
end

lemma bset2d.subset_remove_same {l1 l2 : bset2d} {xy : ℕ×ℕ}
  : l1 ⊆ l2 → l1.remove xy ⊆ l2.remove xy
:= begin
  intros Hsub xy' Hin, apply bset2d.mem_remove_of_neq_mem,
  exact bset2d.neq_of_mem_remove Hin,
  apply Hsub,
  exact bset2d.mem_of_mem_remove Hin,
end

--                         _                             _       _       
--    ___ ___  _   _ _ __ | |_     _     _   _ _ __   __| | __ _| |_ ___ 
--   / __/ _ \| | | | '_ \| __|  _| |_  | | | | '_ \ / _` |/ _` | __/ _ \
--  | (_| (_) | |_| | | | | |_  |_   _| | |_| | |_) | (_| | (_| | ||  __/
--   \___\___/ \__,_|_| |_|\__|   |_|    \__,_| .__/ \__,_|\__,_|\__\___|
--                                            |_|                        

lemma bset1d.count_update : ∀ (b : bool) (l : bset1d) (n : ℕ),
∃ c, bset1d.count l = c + (list.func.get n l).to_nat
∧ bset1d.count (list.func.set b l n) = c + b.to_nat
:=
list.sum_map_update bool.to_nat rfl 

lemma bset2d.count_update : ∀ (b : bool) (l : bset2d) (xy : ℕ×ℕ),
∃ c, bset2d.count l = c + (list2d.get2d xy l).to_nat
∧ bset2d.count (list2d.set2d b l xy) = c + b.to_nat
:=
begin
  intros, cases xy with x y,
  rcases list.sum_map_update bset1d.count rfl
    (list.func.set b (list.func.get y l) x) l y
  with ⟨c1, H1old, H1new⟩,
  rcases bset1d.count_update b (list.func.get y l) x
  with ⟨c2, H2old, H2new⟩,
  existsi c1 + c2,
  split, {
    unfold bset2d.count, rw H1old, rw H2old,
    rw ←add_assoc, refl,
  }, {
    unfold bset2d.count, unfold list2d.set2d,
    rw H1new, rw H2new, rw ←add_assoc,
  }
end

lemma bset2d.count_add {xy : ℕ×ℕ} {l : bset2d}
: xy ∉ l → (l.add xy).count = l.count+1
:=
begin
  rcases bset2d.count_update tt l xy with ⟨c,Hold,Hnew⟩,
  assume Hnin : xy ∉ l,
    rw bool_eq_false Hnin at Hold, clear Hnin,
  unfold bset2d.add, rw Hnew, rw Hold,
  simp [bool.to_nat],
end

lemma bset2d.count_remove {xy : ℕ×ℕ} {l : bset2d}
: xy ∈ l → (l.remove xy).count+1 = l.count
:=
begin
  rcases bset2d.count_update ff l xy with ⟨c,Hold,Hnew⟩,
  assume Hin : xy ∈ l,
    rw bset2d.has_mem.unfold at Hin, rw Hin at Hold, clear Hin,
  unfold bset2d.remove, rw Hnew, rw Hold,
  simp [bool.to_nat],
end

--           _ _  __  __ 
--   ___  __| (_)/ _|/ _|
--  / __|/ _` | | |_| |_ 
--  \__ \ (_| | |  _|  _|
--  |___/\__,_|_|_| |_|  
--                       

lemma bset2d.mem_sdiff_of_mem_nmem {xy : ℕ×ℕ} {l1 l2 : bset2d}
  : xy ∈ l1 → xy ∉ l2 → xy ∈ l1 \ l2 :=
begin
  simp [has_sdiff.sdiff, has_mem.mem, list2d.get2d_pointwise],
  intros H1 H2, simp! [H1, H2],
end
lemma bset2d.mem_of_mem_sdiff {xy : ℕ×ℕ} {l1 l2 : bset2d}
  : xy ∈ l1 \ l2 → xy ∈ l1 :=
begin
  simp [has_sdiff.sdiff, has_mem.mem, list2d.get2d_pointwise],
  assume H, cases (list2d.get2d xy l2), exact H, exact bool.no_confusion H,
end
lemma bset2d.nmem_of_mem_sdiff {xy : ℕ×ℕ} {l1 l2 : bset2d}
  : xy ∈ l1 \ l2 → xy ∉ l2 :=
begin
  simp [has_sdiff.sdiff, has_mem.mem, list2d.get2d_pointwise],
  assume H, cases (list2d.get2d xy l2), refl, exact bool.no_confusion H,
end
lemma bset2d.sdiff_subset {l1 l2 : bset2d} : l1 \ l2 ⊆ l1
:= assume xy, bset2d.mem_of_mem_sdiff

--   _       _                                  _             
--  (_)_ __ | |_ ___ _ __     _     _   _ _ __ (_) ___  _ __  
--  | | '_ \| __/ _ \ '__|  _| |_  | | | | '_ \| |/ _ \| '_ \ 
--  | | | | | ||  __/ |    |_   _| | |_| | | | | | (_) | | | |
--  |_|_| |_|\__\___|_|      |_|    \__,_|_| |_|_|\___/|_| |_|
--                                                            

lemma bset2d.inter_subset_left {l1 l2 : bset2d} : l1 ∩ l2 ⊆ l1
:=
  assume xy,
  assume H,
  have this : list2d.get2d xy l1 && list2d.get2d xy l2 = tt
    := eq.trans (eq.symm (list2d.get2d_pointwise rfl _ _ _)) H,
  show xy ∈ l1, from ((band_coe_iff _ _).mp this).1

lemma bset2d.inter_subset_right {l1 l2 : bset2d} : l1 ∩ l2 ⊆ l2
:=
  assume xy,
  assume H,
  have this : list2d.get2d xy l1 && list2d.get2d xy l2 = tt
    := eq.trans (eq.symm (list2d.get2d_pointwise rfl _ _ _)) H,
  show xy ∈ l2, from ((band_coe_iff _ _).mp this).2

lemma bset2d.union_subset {l1 l2 l3 : bset2d} : l1 ⊆ l3 → l2 ⊆ l3 → l1 ∪ l2 ⊆ l3
:=
begin
  assume H1 H2 xy Hin,
  have this : list2d.get2d xy l1 || list2d.get2d xy l2 = tt
    := eq.trans (eq.symm (list2d.get2d_pointwise rfl _ _ _)) Hin,
  cases (bor_coe_iff _ _).mp this with Hin1 Hin2,
  exact H1 xy Hin1,
  exact H2 xy Hin2,
end
lemma bset2d.union_supset_left {l1 l2 : bset2d} : l1 ⊆ l1 ∪ l2
:=
begin
  assume xy,
  assume H,
  refine eq.trans (list2d.get2d_pointwise rfl _ _ _) _,
  exact (congr_arg (λ a, a || list2d.get2d xy l2) H).trans (tt_bor _),
end
lemma bset2d.union_supset_right {l1 l2 : bset2d} : l2 ⊆ l1 ∪ l2
:=
begin
  assume xy,
  assume H,
  refine eq.trans (list2d.get2d_pointwise rfl _ _ _) _,
  exact (congr_arg (bor _) H).trans (bor_tt _),
end


--   _           _                    
--  (_)_ __   __| | _____  _____  ___ 
--  | | '_ \ / _` |/ _ \ \/ / _ \/ __|
--  | | | | | (_| |  __/>  <  __/\__ \
--  |_|_| |_|\__,_|\___/_/\_\___||___/
--                                    

def bset2d.from_index (xy : ℕ×ℕ) : bset2d := list2d.set2d tt [] xy
def bset2d.from_indexes (xys : list (ℕ × ℕ)) : bset2d
:= list.foldr (λ (xy : ℕ×ℕ) (l : bset2d), l.set2d tt xy) [] xys
def bset2d.to_indexes (s : bset2d) : list (ℕ × ℕ)
:= s.find_indexes2d (eq tt)

theorem bset2d.from_index_iff (xy : ℕ×ℕ)
  : ∀ xy' : ℕ×ℕ, xy' ∈ bset2d.from_index xy ↔ xy' = xy :=
begin
  intro xy', split, {
    intro H, by_contradiction C,
    unfold has_mem.mem at H, unfold bset2d.from_index at H,
    rw list2d.get2d_set2d_eq_of_ne at H, simp at H, exact H, exact C,
  }, {
    intro H, rw H, unfold bset2d.from_index, unfold has_mem.mem,
    exact list2d.get2d_set2d,
  }
end

theorem bset2d.from_indexes_iff (xys : list (ℕ×ℕ))
  : ∀ xy : ℕ×ℕ, xy ∈ bset2d.from_indexes xys ↔ xy ∈ xys :=
begin
  intro xy, induction xys with xy' t IH, {
    simp! [bset2d.from_indexes, has_mem.mem],
  }, {
    by_cases C : xy = xy',
    { rw ←C, simp! [has_mem.mem, bset2d.from_indexes, list2d.get2d_set2d], },
    simp [bset2d.from_indexes], unfold has_mem.mem,
    rw list2d.get2d_set2d_eq_of_ne C,
    split,
    { intro H, right, exact IH.mp H, },
    { intro H, cases H, exact false.elim (C H),
      exact IH.mpr H, },
  },
end

theorem bset2d.to_indexes_iff (s : bset2d)
  : ∀ xy : ℕ×ℕ, xy ∈ bset2d.to_indexes s ↔ xy ∈ s :=
begin
  intro xy,
  unfold bset2d.to_indexes, rw bset2d.has_mem.unfold,
  rw ←list2d.find_indexes2d_iff, exact eq_comm, simp!,
end
