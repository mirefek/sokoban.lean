import tactic

universes u v

inductive reachable {α : Type u} (P : α → α → Prop) : α → α → Prop
| refl (a : α) : reachable a a
| step {a b c : α} (H1 : P a b) (H2 : reachable b c) : reachable a c

namespace reachable

variable {α : Type u}
variable (P : α → α → Prop)

theorem single_step (a b : α) : P a b → reachable P a b :=
  assume H : P a b, step H (refl b)

theorem trans (a b c : α)
  : reachable P a b → reachable P b c → reachable P a c :=
begin
  intros, induction a_1, exact a_2,
  exact (step a_1_H1 (a_1_ih a_2))
end

theorem iffP (P' : α → α → Prop) (H : ∀ a b, P a b ↔ P' a b)
  : ∀ a b, reachable P a b ↔ reachable P' a b :=
begin
  have : P = P' := funext (λ a, funext (λ b, propext (H a b))),
  rewrite this,
  intros, exact iff.rfl,
end

theorem swapP
  : ∀ a b : α, reachable P b a → reachable (function.swap P) a b :=
begin
  intros a b H, induction H with a, exact refl a,
  exact trans _ _ _ _ H_ih (single_step _ _ _ H_H1),
end
theorem swapP2
  : ∀ a b : α, reachable (function.swap P) b a → reachable P a b :=
begin
  intros a b H, have H := swapP _ _ _ H,
  revert H, apply (iffP _ _ _ _ _).1, simp,
end

def set_reachable (A B : set α) : Prop :=
  ∃ (a ∈ A) (b ∈ B), reachable P a b

theorem set_enlarge (A B A2 B2 : set α)
  (HA : A ⊆ A2) (HB: B ⊆ B2)
  (H : set_reachable P A B)
  : set_reachable P A2 B2 :=
begin
  cases H with a H, cases H with Ha H,
  cases H with b H, cases H with Hb H,
  existsi a, existsi HA Ha,
  existsi b, existsi HB Hb,
  exact H
end
theorem set_singleton (a b : α)
  : reachable P a b ↔ set_reachable P ({a}) ({b}) :=
begin
  split, introv H,
    existsi a, split, simp!, existsi b, split, simp!, exact H,
  intro H, cases H with a1 H, cases H with Ha H,
    cases H with b1 H, cases H with Hb H,
    simp at Ha, simp at Hb,
    rw [←Ha, ←Hb], exact H,
end

def strongly_connected (A : set α) : Prop := 
  ∀ a b : α, a ∈ A → b ∈ A → reachable P a b

theorem set_trans (A B C : set α)
  (HAB : set_reachable P A B)
  (HB : strongly_connected P B)
  (HBC : set_reachable P B C)
  : set_reachable P A C :=
begin
  cases HAB with a HAB, cases HAB with Ha HaB,
  cases HaB with b1 HaB, cases HaB with Hb1 Hab,
  cases HBC with b2 HBC, cases HBC with Hb2 HbC,
  cases HbC with c HbC, cases HbC with Hc Hbc,
  existsi a, existsi Ha, existsi c, existsi Hc,
  apply trans _ _ b1, exact Hab,
  apply trans _ _ b2, exact (HB _ _ Hb1 Hb2),
  exact Hbc,
end

theorem strongly_connected_singleton
  : ∀ x : α, strongly_connected P ({x}) :=
begin
  intros x a b Ha Hb, simp at Ha, simp at Hb,
  rw [Ha, Hb], exact refl x,
end
theorem strongly_connected_empty
  : strongly_connected P ∅ :=
begin
  intros a b Ha, simp at Ha, contradiction,
end
theorem unreachable_empty1 (B : set α)
  : ¬ set_reachable P ∅ B :=
begin
  intros H,
  cases H with a H, cases H with Ha H,
  exact Ha,
end
theorem unreachable_empty2 (A : set α)
  : ¬ set_reachable P A ∅ :=
begin
  intros H,
  cases H with a H, cases H with Ha H, cases H with b H, cases H with Hb H,
  exact Hb,
end

theorem path_split (A B : set α) (a c : α)
  (HA : A a) (HAB : ∀ a b, P a b → a ∈ A → b ∈ A ∨ b ∈ B)
  (Hnac : c ∉ A)
  (H : reachable P a c)
  : ∃ b ∈ B,
  reachable P a b ∧ reachable P b c :=
begin
  induction H with a a b c, exact absurd HA Hnac,
  cases HAB a b H_H1 HA with HAb HBb,
    cases H_ih HAb Hnac with b' H_ih, cases H_ih with Hb' H_ih,
    cases H_ih with H_bb' Hb'c,
    existsi b', split, exact Hb',
    split, exact step H_H1 H_bb', exact Hb'c,
  existsi b, split, exact HBb,
  split, exact single_step P a b H_H1, exact H_H2,
end

#check (↑[1, 2, 3].to_finset : set ℕ)

theorem set_step_s (As Bs : set (set α)) (C : set α)
  (HAs : ∀ A : set α, A ∈ As → ∀ a b : α, a ∈ A → P a b →
    ∃ B : set α, (B ∈ As ∨ B ∈ Bs) ∧ b ∈ B)
  (HnC : ∀ A : set α, A ∈ As → ∀ a : α, a ∈ A → a ∉ C)
  (A : set α) (HA : A ∈ As)
  (H : set_reachable P A C)
  : ∃ B ∈ Bs, set_reachable P A B ∧ set_reachable P B C :=
begin
  cases H with a H, cases H with Ha H,
  cases H with c H, cases H with Hc H,
  let Au : set α := set.sUnion As,
  let Bu : set α := set.sUnion Bs,
  have Hb := path_split P Au Bu a c,
  specialize Hb _, { show a ∈ Au,
    clear Hb Bu H Hc c HnC HAs C P,
    simp, existsi A, split, exact HA, exact Ha,
  },
  specialize Hb _, {
    clear Hb H Hc c Ha a HA A HnC C,
    introv H1 H2, simp at H2,
    cases H2 with A H2, cases H2 with HA Ha,
    cases HAs A HA a b Ha H1 with B H,
      cases H with HAB Hb, cases HAB,
        left, simp, existsi B, split, exact HAB, exact Hb,
      right, simp, existsi B, split, exact HAB, exact Hb,
  },
  specialize Hb _, { show c ∉ Au,
    clear Hb Bu H Ha a HA A HAs Bs P,
    simp, intros A HA HAc, exact HnC A HA c HAc Hc,
  },
  cases Hb H with b Hb, cases Hb with Hb H,
  cases H with Hab Hbc, cases Hb with B Hb,
  cases Hb with HB Hb,
  existsi B, existsi HB, split,
  { existsi a, existsi Ha, existsi b, existsi Hb, exact Hab, },
  { existsi b, existsi Hb, existsi c, existsi Hc, exact Hbc, },
end

theorem set_step_l (Al Bl : list (set α)) (C : set α)
  (HAl : ∀ A : set α, A ∈ Al → ∀ a b : α, a ∈ A → P a b →
    ∃ B : set α, (B ∈ Al ∨ B ∈ Bl) ∧ b ∈ B)
  (HnC : ∀ A : set α, A ∈ Al → ∀ a : α, a ∈ A → a ∉ C)
  (A : set α) (HA : A ∈ Al)
  (H : set_reachable P A C)
  : ∃ B ∈ Bl, set_reachable P A B ∧ set_reachable P B C
:=
set_step_s P {A | A ∈ Al} {B | B ∈ Bl} C HAl HnC A HA H

theorem factor1 {β : Type v} (Q : β → β → Prop) (f : α → β)
  (HP : ∀a1 a2 : α, P a1 a2 → f a1 = f a2 ∨ Q (f a1) (f a2))
  : ∀ a1 a2, reachable P a1 a2 → reachable Q (f a1) (f a2) :=
begin
  intros a1 a2 H, induction H, exact refl (f H),
    cases HP _ _ H_H1 with Heq HQ,
      rewrite Heq, exact H_ih,
      exact step HQ H_ih,
end

theorem factor2 {β : Type v} (Q : β → β → Prop) (f : α → β)
  (H1 : ∀b : β, strongly_connected P (f⁻¹' {b}))
  (H2 : ∀b1 b2 : β, Q b1 b2 → ∃a1 a2 : α, f a1 = b1 ∧ f a2 = b2 ∧ P a1 a2)
  :  ∀ a1 a2, reachable Q (f a1) (f a2) → reachable P a1 a2 :=
begin
  intros a1 a2, generalize E1 : f a1 = b1, generalize E2 : f a2 = b2,
  intro H, revert a1, induction H with b1 b0 b1 b2, {
    intros, apply H1 b1 a1 a2, simp [E1], simp [E2],
  }, {
    intros a0 E0,
    cases H2 b0 b1 H_H1 with a0' H, cases H with a1 H,
    cases H with E0' H, cases H with E1 HP,
    apply trans _ _ a0',
    apply H1 b0 a0 a0', simp [E0], simp [E0'],
    exact step HP (H_ih E2 a1 E1),
  }
end

end reachable
