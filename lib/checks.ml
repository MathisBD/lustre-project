open Typed_ast
open Typed_ast_utils

(* Verifying scheduling. *)

exception Scheduling of t_node

let defs_of_patt patt acc =
  List.fold_left (fun acc x -> Scheduling.S.add x acc) acc patt.tpatt_desc

let deps_of_expr =
  let rec deps_of_expr expr acc =
    match expr.texpr_desc with
    | TE_ident x -> (expr, Scheduling.S.add x acc)
    | TE_pre _ -> (expr, acc)
    | TE_arrow (e1, _) -> deps_of_expr e1 acc
    | TE_const _
    | TE_unop (_, _)
    | TE_binop (_, _, _)
    | TE_app (_, _)
    | TE_prim (_, _)
    | TE_if (_, _, _)
    | TE_tuple _ | TE_print _ ->
        expr_map_fold deps_of_expr expr acc
  in
  fun expr -> snd (deps_of_expr expr Scheduling.S.empty)

let scheduled_node node =
  let defs =
    List.fold_left
      (fun acc (x, _) -> Scheduling.S.add x acc)
      Scheduling.S.empty node.tn_input
  in
  let _ =
    List.fold_left
      (fun defs eq ->
        let deps = deps_of_expr eq.teq_expr in
        if Scheduling.S.subset deps defs
        then defs_of_patt eq.teq_patt defs
        else raise (Scheduling node))
      defs node.tn_equs
  in
  ()

let scheduling f =
  try List.iter scheduled_node f
  with Scheduling n -> Format.eprintf "Warning: node %s is not scheduled.@." n.tn_name
