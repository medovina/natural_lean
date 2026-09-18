import Natural.Proof

open Lean
open Lean.Elab.Command
open Lean.Parser.Command
open Lean.Parser.Term
open Lean.Syntax

namespace Natural

def of_label: TSyntax ``label → CoreM Name
  | `(label| $i:ident) => pure i.getId
  | _ => throwError "unknown label"

def label_range (i j: Name) : CoreM (List Name) :=
  match i.toString.toList, j.toString.toList with
    | [c], [d] => pure $ (c ...= d).toList.map (Name.mkSimple ∘ Char.toString)
    | _, _ => throwError "label must be a single letter"

def of_proof_item: TSyntax ``proof_item → CoreM (List (Name × _Proof))
  | `(proof_item| $i:label $[- $j:label]? . $p:proof) => do
      let (i, j) ← pairM (of_label i) (j.mapM of_label)
      let p ← of_proof p
      match j with
        | .some j => .map (·, p) <$> label_range i j
        | .none => pure [(i, p)]
  | _ => throwError "unknown proof_item"

def of_proof_items: TSyntax ``proof_items → CoreM (List (Name × _Proof))
  | `(proof_items| $ps:proof_item*) => ps.toList.flatMapM of_proof_item
  | _ => throwError "unknown proof_items"

-- definitions

def of_constructor: TSyntax ``constructor → CoreM (Term × Term)
  | `(constructor| $c:const : $t:type) => do pure (← of_const c, ← of_type t)
  | _ => throwError "unknown constructor"

def nat_instance (type: Term) (num: NumLit) (expr: Term) : CoreM Command :=
  `(instance: $(mkIdent ``OfNat) $type $num where
              $(mkIdent `ofNat):ident := $expr)

def aux_ctor_def (typ:Ident) (t: Term): CoreM Command :=
  let dot (i: Ident) := mkIdent (typ.getId ++ i.getId)
  match t with
    | `($n:num) => nat_instance typ n (dot (to_ident t))
    | `($i:ident) => `(abbrev $i := $(dot i))
    | _ => throwError "aux_ctor_def: unknown"

def command_set (commands: List Command) : CoreM Command := do
  let ctrace cmd := do
    trace[natural] cmd
    pure ()
  commands.forM ctrace
  pure $ .mk (mkNullNode commands.toArray)

def op_fun (op: TSyntax α) (type: Term) : CoreM Term := do
  let apply_op := build_infix (← `(x)) (of_binary_op op) (← `(y))
  `(fun x y : $type => $apply_op)

def of_inductive_def (name: Ident): TSyntax ``inductive_def → CoreM (List Command)
  | `(inductive_def| inductively with constructors $cs:constructor and* .) => do
    let ctors ← cs.getElems.mapM of_constructor
    let mk_def | (n, t) => `(ctor| | $(to_ident n):ident : $t)
    let ctor_defs ← ctors.mapM mk_def
    let ind_decl ← `(inductive $name:ident $ctor_defs:ctor*)
    let aux ← (ctors.map (·.1)).mapM (aux_ctor_def name)
    pure $ [ind_decl] ++ aux.toList
  | _ => throwError "unknown inductive_def"

def of_justification : TSyntax ``justification → CoreM Ident
  | `(justification| Justification . By $thm:thm_name .) => of_thm_name thm
  | _ => throwError "unknown justification"

def of_quotient_def (i: Ident): TSyntax ``quotient_def → CoreM (List Command)
  | `(quotient_def| as the quotient $t:type / $op:rel_op . $j:justification) => do
      let type ← of_type t
      let inst_name := mkIdent (i.getId ++ `Setoid)
      let inst_cmd ← `(instance $inst_name:ident : Setoid ($type) where
        r := $(← op_fun op type)
        iseqv := $(← proof_by (.some (← of_justification j))))
      let quot_cmd ← `(def $i := Quotient ($inst_name))
      pure [inst_cmd, quot_cmd]
  | _ => throwError "unknown quotient_def"

def of_type_spec (i: Ident): TSyntax `type_spec → CoreM (List Command)
  | `(type_spec| $id:inductive_def) => of_inductive_def i id
  | `(type_spec| $qd:quotient_def) => of_quotient_def i qd
  | _ => throwError "unknown type_spec"

def of_type_def : TSyntax ``type_def → CoreM (List Command)
  | `(type_def| The type $i:ident $[( the $n1:ident $n2:ident ?)]?
                is defined $ts:type_spec) => do
      let commands ← of_type_spec i ts
      let att ← n1.mapM (fun n1 =>
        let t := idents_to_nat_type n1 (n2.get!)
        `(attribute [natural_name $(mkStrLit t)] $i:ident)
      )
      pure $ commands ++ att.toList
  | _ => throwError "unknown definition"

def of_attrib: TSyntax ``attrib → CoreM Ident
  | `(attrib| @ $i:ident) => pure i
  | _ => throwError "unknown attrib"

def of_post_name : TSyntax ``post_name → CoreM (Option Ident × Option Ident)
  | `(post_name| $[ [ $i:thm_name $[ : $a:attrib ]? ] ]? ) => do
      pure (← i.mapM of_thm_name, ← a.join.mapM of_attrib)
  | _ => throwError "unknown post_name"

def of_top_sentence : TSyntax ``top_sentence → CoreM (Term × Option Ident × Option Ident)
  | `(top_sentence| $p:prop . $pn:post_name) => do
      pure (← of_prop p, ← of_post_name pn)
  | _ => throwError "unknown top_sentence"

abbrev Label := Name

structure ThmDecl where
  label: Option Label
  thm: Term
  name: Option Ident
  attr: Option Ident

def of_prop_item : TSyntax ``prop_item → CoreM ThmDecl
  | `(prop_item| $i:label . $s:top_sentence) => do
      let (thm, name, attr) ← of_top_sentence s
      pure ⟨← of_label i, thm, name, attr⟩
  | _ => throwError "unknown prop_item"

def parse_def_eq : Term → CoreM (String × Term × Term × Term)
  | `($l = $r)
  | `($l ↔ $r) => do
      let (a, op, b) ← parse_infix l
      pure (map_op op, a, b, r)
  | _ => throwError "equation expected"

def eq_to_alt_expr (op: String) (fname: Ident) (t: Term): CoreM (TSyntax ``matchAltExpr) := do
  let (op', a, b, r) ← parse_def_eq t
  if op == op' then
    `(matchAltExpr| | $a, $b => $(replace_infix op fname r))
  else throwError "wrong infix op"

partial def pattern_type (arg_names: List Name) (arg_type: Ident) : Term → CoreM Term :=
  let rec f : Term → CoreM Term
    | `($x:ident) =>
        if arg_names.elem x.getId then pure arg_type
          else throwError "undefined variable in pattern"
    | `(($t, $u)) => do `($(← f t) × $(← f u))
    | _ => throwError "unrecognized pattern in definition"
  f

partial def flat_name : Term → CoreM String
  | `($i:ident) => pure i.getId.toString
  | `($t × $u) => do pure $ (← flat_name t) ++ "_" ++ (← flat_name u)
  | _ => throwError "flat_name: can't encode"

def embed_name (type: Term) (name: Name) : CoreM Ident := mkIdent <$> match type with
  | `($i:ident) => pure $ i.getId ++ name
  | _ => do pure $ Name.mkSimple ((← flat_name type) ++ "_" ++ name.toString)

def generate_op_def (op: String) (args: List Ident) (arg_type: Ident) (eqs: Array Term)
    (justification: Option Ident) : CoreM (List Command) := do
  let (op_name, cl) ← (op_class.lookup op).getDM $ throwError "generate_def: no op"
  let arg_fname ← embed_name arg_type op_name
  let arg_names := args.map (·.getId)
  let eqs ← eqs.mapM (resolve_term (arg_names.map (·, arg_type)))
  let (def_cmds, op_type, fname) ← match eqs with
    | #[eq] =>  -- direct function definition
        let (_op, x, y, r) ← parse_def_eq eq
        match x, y with
          | `($ix:ident), `($iy:ident) => do
              let d ← `(def $arg_fname ($ix $iy : $arg_type) := $r)
              pure ([d], arg_type, arg_fname)
          | `( (Quotient.mk' $x : $qx:ident) ), `( (Quotient.mk' $y : $qy:ident) ) => do
              let op_type := qx
              let aux_name ← embed_name op_type (op_name ++ `aux)
              let (tx, ty) ← mapM_pair (pattern_type arg_names arg_type) (x, y)
              let aux ← `(def $aux_name | ($x : $tx), ($y : $ty) => $r)
              let by_thms ← proof_by_multi (mkIdent ``Quotient.sound :: justification.toList)
              let fname ← embed_name op_type op_name
              let d ← `(def $fname (a: $qx) (b: $qy) : $qx :=
                Quotient.lift₂ $aux_name $by_thms a b)
              pure ([aux, d], op_type, fname)
          | _, _ =>
              let (tx, ty) ← mapM_pair (pattern_type arg_names arg_type) (x, y)
              let name ← embed_name tx op_name
              ([·], ⟨tx⟩, name) <$> `(def $name | ($x : $tx), ($y : $ty) => $r)
    | _ => do  -- by cases
        let alts ← eqs.mapM (eq_to_alt_expr op arg_fname)
        let c ← `(set_option linter.unusedVariables false in
          def $arg_fname : $arg_type → $arg_type → $arg_type
            $alts:matchAlt*)
        pure ([c], arg_type, arg_fname)

  -- Declare that the function we defined implements the operator (op).
  let instName ← embed_name op_type (Name.mkSimple ("inst" ++ cl.toString))
  let i ← `(
    @[method_specs]
    instance $instName:ident : $(mkIdent cl) $(⟨op_type⟩) where
      $(mkIdent op_name):ident := $fname
  )

  -- Add an attribute for grind.
  let spec := instName.getId ++ Name.mkSimple (op_name.toString ++ "_spec")
  let a ← `(attribute [grind =] $(mkIdent spec))
  pure (def_cmds ++ [i, a])

def infer_type : TSyntax `expr → CoreM Term
  | `(expr| $t:ident [ $_:expr ]) => pure t
  | _ => throwError "must specify constant type"

def of_direct_def : TSyntax `direct_def → CoreM (List Command)
  | `(direct_def| $_:_for_all $ids_type:ids_type , $p:prop . $just:justification ?) => do
      let (args, type) ← of_ids_type ids_type
      let eq ← of_prop p
      let (op, _, _, _) ← parse_def_eq eq
      match type with
        | `($type:ident) =>
              generate_op_def op args.toList type #[eq] (← just.mapM of_justification)
        | _ => throwError "simple type expected"
  | `(direct_def| $n:num $[: $type:type]? = $e:expr .) => do
      let expr ← of_expr e >>= resolve_term []
      let type ← type.elim (infer_type e) of_type
      pure [← nat_instance type n expr]
  | _ => throwError "unknown direct_def"

def of_cases_def : TSyntax ``cases_def → CoreM (List Command)
  | `(cases_def| The $_:_operator $op:binary_op on $type:ident is defined recursively
                    such that for all $ids_type:ids_type , $items:prop_item*) => do
      let (xs, _type) ← of_ids_type ids_type
      let eqs ← Array.map ThmDecl.thm <$> items.mapM of_prop_item
      generate_op_def (of_binary_op op) xs.toList type eqs none
  | _ => throwError "unknown cases_def"

def of_definition : TSyntax `definition → CoreM (List Command)
  | `(definition| $d:type_def) => of_type_def d
  | `(definition| $d:direct_def) => of_direct_def d
  | `(definition| $e:cases_def) => of_cases_def e
  | _ => throwError "unknown definition"

-- theorems

def match_proofs : List ThmDecl → List (Label × _Proof) → CoreM (List (ThmDecl × Option _Proof))
  | [], [] => pure []
  | decl :: ts, (j, proof) :: ps =>
      if decl.label == j then .cons (decl, .some proof) <$> match_proofs ts ps
      else .cons (decl, .none) <$> match_proofs ts ((j, proof) :: ps)
  | decl :: ts, [] => .cons (decl, .none) <$> match_proofs ts []
  | [], (j, _) :: _ => throwError s!"unmatched proof label: {j}"

def lets_vars (lets: Option ProofStep) : LocalEnv := match lets with
  | .none => []
  | .some (.let ids type) => ids.map (·, type)
  | _ => panic! "lets_vars: unexpected step"

def translate_proofs (lets: Option ProofStep) (thms_proofs: List (ThmDecl × Option _Proof))
    : CoreM (List (ThmDecl × Option Term)) :=
  thms_proofs.mapM (fun (decl, proof) => withRef decl.thm do
    let thm ← resolve_term (lets_vars lets) decl.thm
    pure ({decl with thm := ← generalize lets thm},
          ← proof.mapM (translate_proof lets thm)))

def of_props_proofs (lets: Option ProofStep) (ps: TSyntax `props_proofs) :
        CoreM (List (ThmDecl × Option Term)) :=
  match ps with
    | `(props_proofs| $s:top_sentence $[ $_:_proof_dot $proof:proof ]?) => do
        let (thm, opt_name, opt_attr) ← of_top_sentence s
        let decl := ThmDecl.mk none thm opt_name opt_attr
        translate_proofs lets [(decl, ← proof.mapM of_proof)]
    | `(props_proofs| $ps:prop_item* $[ $_:_proof_dot $pis:proof_items ]?) => do
        let label_thms ← ps.toList.mapM of_prop_item
        let label_proofs := (← pis.mapM of_proof_items).getD []
        let thms_proofs ← match_proofs label_thms label_proofs
        translate_proofs lets thms_proofs
    | _ => throwError "unknown prop_or_items"

def mk_decl (is_instance: Bool) (attr: Option Ident) (name: Option Ident)
            (thm proof: Term) : CoreM Command := do
  let a ← attr.mapM (fun a => `(attributes| @[$a:ident]))
  if is_instance then `($a:attributes ? instance $[$name:ident]? : $thm := $proof)
  else match name with
    | Option.some name => `($a:attributes ? theorem $name : $thm := $proof)
    | Option.none => `($a:attributes ? example : $thm := $proof)

def of_theorem_body (name: Option Ident) (corollary_of: List Ident)
          (body: TSyntax `theorem_body) : CoreM (List Command × List Ident) := do
  let by_default : Option Ident := match corollary_of with
    | [c] => Option.some c  -- use corollary_of by default if there is just one
    | _ => .none
  match body with
    | `(theorem_body| $[$ls:let_step .]? $ps:props_proofs) => do
        let thms_proofs ← of_props_proofs (← ls.mapM of_let_step) ps
        let (commands, names) := List.unzip $ ← thms_proofs.mapM
          (fun (⟨label, thm, thm_name, attr⟩, proof) => withRef thm do
            let proof := proof.getD (← proof_by by_default)
            let name := thm_name <|> name.map (fun name =>
              label.elim name (mkIdent $ name.getId ++ ·))
            let command ← mk_decl false attr name thm proof
            pure (command, name))
        pure (commands, (names.flatMap Option.toList))
    | `(theorem_body| The $_:_operator $op:binary_op is $_:_a ? $kind:natural_type
                      on $type:type . $pn:post_name) => do
        let env ← getEnv
        let kind ← of_natural_type kind  -- name of type class or structure
        unless Lean.isStructure env kind.getId do throwError "not a structure"
        let type ← of_type type
        let (name, attr) ← of_post_name pn
        let thm ← `($kind $(← op_fun op type))
        let fields := Lean.getStructureFieldsFlattened env kind.getId false
        let corollary_for (field: Name) :=
          corollary_of.find? (fun c => c.getId.toString.endsWith field.toString)
        let proofs ← fields.mapM (fun f => proof_by (corollary_for f <|> by_default))
        let command ← mk_decl (Lean.isClass env kind.getId) attr name thm (← `(⟨$proofs,*⟩))
        pure ([command], [])
    | _ => throwError "unknown theorem"

def of_theorem (corollary_of: List Ident)
            : TSyntax ``_theorem → CoreM (List Command × List Ident)
    | `(_theorem| $name:thm_name ? $_:str ? . $b:theorem_body) => do
        let name ← name.mapM of_thm_name
        of_theorem_body name corollary_of b
    | _ => throwError "unknown theorem"

def of_top_decl : TSyntax `top_decl → CoreM (List Command × List Ident)
  | `(top_decl| Definition . $d) => (·, []) <$> of_definition d
  | `(top_decl| $_:_thm $t:_theorem) => of_theorem [] t
  | _ => throwError "unknown top_decl"

elab t:top : command => do
  let cs : Command ← liftCoreM $ command_set =<< match t with
    | `(top| $d:top_decl $[Corollary $ts:_theorem]*) => do
        let (commands, names) ← of_top_decl d
        let corrs ← List.map (·.1) <$> ts.toList.mapM (of_theorem names)
        pure $ commands ++ corrs.flatten
    | _ => throwError "unknown top"
  elabCommand cs
