(* semantic.ml *)

module A = Absyn
module S = Symbol
module T = Type

type entry = [%import: Env.entry]
type env = [%import: Env.env]

(* Obtain the location of an ast *)

let loc = Location.loc

(* Reporting errors *)

let undefined loc category id =
  Error.error loc "undefined %s %s" category (S.name id)

let misdefined loc category id =
  Error.error loc "%s is not a %s" (S.name id) category

let type_mismatch loc expected found =
  Error.error loc "type mismatch: expected %s, found %s" (T.show_ty expected) (T.show_ty found)

(* Searhing in symbol tables *)

let look env category id pos =
  match S.look id env with
  | Some x -> x
  | None -> undefined pos category id

let tylook tenv id pos =
  look tenv "type" id pos

let varlook venv id pos =
  match look venv "variable" id pos with
  | VarEntry t -> t
  | FunEntry _ -> misdefined pos "variable" id

let funlook venv id pos =
  match look venv "function" id pos with
  | VarEntry _ -> misdefined pos "function" id
  | FunEntry (params, result) -> (params, result)

(* Type compatibility *)

let compatible ty1 ty2 pos =
  if not (T.coerceable ty1 ty2) then
    type_mismatch pos ty2 ty1

(* Set the value in a reference of optional *)

let set reference value =
  reference := Some value;
  value

(* Checking expressions *)

let rec check_exp env (pos, (exp, tref)) =
  match exp with
  | A.BoolExp _ -> set tref T.BOOL
  | A.IntExp  _ -> set tref T.INT
  | A.RealExp _ -> set tref T.REAL
  | A.StringExp _ -> set tref T.STRING
  | A.LetExp (decs, body) -> check_exp_let env pos tref decs body
  | A.BinaryExp (left, op, right) ->
    let tLeft = check_exp env left in
    let tRight = check_exp env right in
    begin match op with
      | A.Plus 
      | A.Minus 
      | A.Div 
      | A.Mod
      | A.Times 
      | A.Power ->
          begin match tLeft, tRight with
            | T.INT,  T.REAL 
            | T.REAL, T.INT 
            | T.REAL, T.REAL -> set tref T.REAL
            | T.INT,  T.INT  -> set tref T.INT
            | _              -> type_mismatch pos tLeft tRight
          end   
      | A.And
      | A.Or ->
        begin match tLeft, tRight with
          | T.BOOL, T.BOOL -> set tref T.BOOL
          | _ -> (match tLeft with
              | T.BOOL -> type_mismatch pos T.BOOL tRight
              | _ -> type_mismatch pos T.BOOL tLeft 
            )
        end
      | A.Equal 
      | A.NotEqual -> compatible tRight tLeft pos; set tref T.BOOL
      | A.LowerThan 
      | A.LowerEqual
      | A.GreaterThan 
      | A.GreaterEqual->
        begin match tLeft with
          | T.STRING -> (match tRight with T.STRING -> set tref T.BOOL |_ -> type_mismatch pos T.STRING tLeft)
          | T.INT -> (match tRight with T.INT ->set tref T.BOOL |_ -> type_mismatch pos T.INT tLeft)
          | T.REAL -> (match tRight with T.REAL -> set tref T.BOOL |_ -> type_mismatch pos T.REAL tLeft)
          | _ -> Error.fatal "unimplemented"
        end 
    end
  | A.BreakExp -> (match env.inloop with
      |true -> T.VOID
      |_ -> Error.error pos "Break error"
      )
  | A.WhileExp (test, body) -> let env' = {env with inloop = true} in
      ignore(check_exp env' test);ignore(check_exp env' body); set tref T.VOID
  | A.NegativeExp (exp) -> let result = check_exp env exp in 
      begin match result with
        | T.REAL -> set tref result
        | T.INT 
        | _ -> type_mismatch pos T.REAL result
      end
  | A.ExpSeq expList ->
    let rec check_seq = function
      | []        -> T.VOID
      | [exp]     -> check_exp env exp
      | exp::rest -> ignore (check_exp env exp); check_seq rest
    in
      check_seq expList
  | _ -> Error.fatal "unimplemented"

(* Checking declarations *)
and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody
and check_dec_var env pos ((name, type_opt, init), tref) =
  let tinit = check_exp env init in
  let tvar =
    match type_opt with
    | Some tname ->
       let t = tylook env.tenv tname pos in
       compatible tinit t (loc init);
       t
    | None -> tinit
  in
  ignore (set tref tvar);
  let venv' = S.enter name (VarEntry tvar) env.venv in
  {env with venv = venv'}

and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | _ -> Error.fatal "unimplemented"

let semantic program =
  check_exp Env.initial program
