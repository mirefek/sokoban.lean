import .list2d
import .boolset2d

namespace sokowidget

meta def attrs_to_with_storekeeper (attrs : list (widget.attr empty)) : widget.html empty :=
  let sk_attrs : list (widget.attr empty) := list.map widget.cn ["v-mid", "dtc", "tc", "gray"] in
  widget.h "div" (sk_attrs++attrs) ["●"]
meta def attrs_to_empty (attrs : list (widget.attr empty)) : widget.html empty :=
  widget.h "div" attrs []
meta def attrs_to_cell (attrs : list (widget.attr empty)) : bool → widget.html empty -- sk
| ff := attrs_to_empty attrs
| tt := attrs_to_with_storekeeper attrs

meta def general_box_attrs : list (widget.attr empty) :=
  list.map widget.cn ["w1", "mw1", "h1"]
meta def unsolved_box_attrs : list (widget.attr empty) :=
  (widget.cn "bg-dark-pink")::general_box_attrs
meta def solved_box_attrs : list (widget.attr empty) :=
  (list.map widget.cn ["ba", "b--black", "bg-dark-green"])++general_box_attrs
meta def storage_box_attrs : list (widget.attr empty) :=
  (list.map widget.cn ["ba", "b--black", "bg-inherited"])++general_box_attrs

meta def get_box_attrs : bool → bool → option (list (widget.attr empty)) -- box, stor
| ff ff := none
| tt ff := some unsolved_box_attrs
| ff tt := some storage_box_attrs
| tt tt := some solved_box_attrs

meta def general_square_attrs : list (widget.attr empty) :=
  list.map widget.cn ["w2", "mw2", "h2"]
meta def wall_square_attrs : list (widget.attr empty) :=
  (widget.cn "bg-black")::general_square_attrs
meta def empty_square_attrs : list (widget.attr empty) :=
  (widget.cn "bg-white-70")::general_square_attrs
meta def blocked_square_attrs : list (widget.attr empty) :=
  (widget.cn "bg-washed-red")::general_square_attrs
meta def get_sq_attrs : bool → bool → list (widget.attr empty) -- av, sbox
| ff _ := wall_square_attrs
| tt ff := blocked_square_attrs
| tt tt := empty_square_attrs

meta def square_with_box (sq_attrs : list (widget.attr empty)) (box : widget.html empty)
: (widget.html empty)
:=
  let sq_attrs2 := (list.map widget.cn
    ["flex", "items-center", "justify-center"])++sq_attrs in
  widget.h "div" sq_attrs2 box

meta def make_square : (bool × bool × bool × bool × bool) → widget.html empty
| (av, sbox, box, stor, sk) :=
  let sq_attrs := get_sq_attrs av sbox in
  match get_box_attrs box stor with
  | none := attrs_to_cell sq_attrs sk
  | some box_attrs := square_with_box sq_attrs (attrs_to_cell box_attrs sk)
  end
meta def make_square_td := (widget.h "td" [widget.cn "pa0"]) ∘ pure ∘ make_square

meta def build_row (r : list (bool × bool × bool × bool × bool)) : widget.html empty
:= (widget.h "tr" [] (r.map make_square_td))

meta def build_table (avail : bset2d) (supboxes : bset2d)
  (boxes : bset2d) (storages : bset2d) (storekeepers : bset2d) :=
  widget.h "table" [widget.cn "collapse"] (list.map build_row
  ((avail.dfzip2d (supboxes.dfzip2d (boxes.dfzip2d (storages.dfzip2d storekeepers))))))

end sokowidget

--#html sokowidget.make_square (tt,tt,tt,ff,ff)
