import .sokolevel

@[reducible] meta def show_sokolevel := tactic
@[reducible] meta def show_sokolevel_w := tactic

open tactic

-- The following two functions are taken from the natural number game and are written by Rob Lewis

meta def copy_decl (prfx : name) (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix prfx

meta def copy_decls (prfx : name) : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive)
  (copy_decl prfx dec)

namespace show_sokolevel

meta def step {α : Type} (t : show_sokolevel α) : show_sokolevel unit :=
t >> return ()

meta def istep := @tactic.istep

meta def solve1 := @tactic.solve1

meta def get_soko_format : tactic format :=
do
  `(sokolevel.solvable %%lev_e) ← tactic.target,
  lev ← tactic.eval_expr sokolevel lev_e,
  return (format.compose "⊢ solvable" (to_string lev))

meta def save_info (p : pos) : show_sokolevel unit :=
do
  s ← tactic.read,
  lev ← get_soko_format <|> return format.nil,
  tactic.save_info_thunk p (λ _, format.compose lev (tactic_state.to_format s))

end show_sokolevel

namespace show_sokolevel_w

meta def step {α : Type} (t : show_sokolevel_w α) : show_sokolevel_w unit :=
t >> return ()

meta def istep := @tactic.istep

meta def solve1 := @tactic.solve1

#check tactic.read

meta def get_soko_widget (s : tactic_state) (lev : sokolevel) : widget.tc unit empty :=
widget.tc.stateless $ λ _,
do
  return [
    widget.h "div" [] [lev.to_html],
    widget.h "hr" [] [],
    widget.h "div" [] [widget.html.of_component s widget.tactic_state_widget]
  ]

#check tactic.save_widget

meta def save_info (p : pos) : show_sokolevel_w unit :=
do
  s ← tactic.read,
  tactic.save_info_thunk p (λ _, tactic_state.to_format s),
  tactic.try (do
    `(sokolevel.solvable %%lev_e) ← tactic.target,
    lev ← tactic.eval_expr sokolevel lev_e,
    s ← tactic.read,
    tactic.save_widget p (widget.tc.to_component (get_soko_widget s lev))
  ),
  return ()
--meta def save_info (p : pos) : show_sokolevel_w unit :=

end show_sokolevel_w

-- maybe, the copying of other tactics is unnecessary...
--run_cmd copy_decls `show_sokolevel.interactive
--run_cmd copy_decls `show_sokolevel_w.interactive
