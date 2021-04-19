import .sokolevel

@[reducible] meta def show_sokolevel := tactic

open tactic

-- The following two functions are taken from the natural number game and are written by Rob Lewis

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `show_sokolevel.interactive

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive) (copy_decl dec)

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
--  tactic.save_widget p (widget.tc.to_component combined_component)

end show_sokolevel

run_cmd copy_decls
