(* Convert abstract syntax trees to generic trees of list of string *)

open Absyn

(* Helper functions *)

let name = Symbol.name
let map  = List.map


(* Format arguments according to a format string resulting in a string *)
let sprintf = Format.sprintf

(* Concatenate the lines of text in the node *)
let flat_nodes tree =
  Tree.map (String.concat "\n") tree

(* Build a singleton tree from a string *)
let mktr s = Tree.mkt [s]

(* Convert a binary operator to a string *)
let stringfy_op op =
  match op with
  | Plus          -> "+"
  | Minus         -> "-"
  | Times         -> "*"
  | Div           -> "/"
  | Mod           -> "%"
  | Power         -> "^"
  | Equal         -> "="
  | NotEqual      -> "<>"
  | GreaterThan   -> ">"
  | GreaterEqual  -> ">="
  | LowerThan     -> "<"
  | LowerEqual    -> "<="
  | And           -> "&&"
  | Or            -> "||"

(* Convert an expression to a generic tree *)
let rec tree_of_exp exp =
  match exp with
  | BoolExp x                 -> mktr (sprintf "BoolExp %b" x) []
  | IntExp x                  -> mktr (sprintf "IntExp %i" x) []
  | RealExp x                 -> mktr (sprintf "RealExp %f" x) []
  | NegativeExp e             -> mktr "NegativeExp" [tree_of_lexp e]
  | BinaryExp (l, op, r)      -> mktr (sprintf "BinaryOp %s" (stringfy_op op)) [tree_of_lexp l; tree_of_lexp r]
  | WhileExp (t, b)           -> mktr "WhileExp" [tree_of_lexp t; tree_of_lexp b]
  | BreakExp                  -> mktr "BreakExp" []
  | ExpSeq seq                -> mktr "ExpSeq" (List.map tree_of_lexp seq)
  | CallExp (f, xs)           -> mktr "CallExp" [mktr (name f) []; mktr "Args" (List.map tree_of_lexp xs)]

(* Convert an anotated expression to a generic tree *)
and tree_of_lexp (_, x) = tree_of_exp x
