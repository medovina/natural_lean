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

def of_id_sig : TSyntax ``id_sig → CoreM (Ident × Option Ident)
  | `(id_sig| $i:ident) => pure (i, none)
  | `(id_sig| $i:ident ( $j:ident )) => pure (i, some j)
  | _ => throwError "unknown base_type"

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

def of_quotient_def (name: Ident): TSyntax ``quotient_def → CoreM (List Command)
  | `(quotient_def| as the quotient $t:type / $op:rel_op . $j:justification) => do
      let type ← of_type t
      let inst_name := mkIdent (name.getId ++ `Setoid)
      let inst_cmd ← `(instance $inst_name:ident : Setoid ($type) where
        r := $(← op_fun op type)
        iseqv := $(← proof_by (.some (← of_justification j))))
      let quot_cmd ← `(def $name := Quotient ($inst_name))
      pure [inst_cmd, quot_cmd]
  | _ => throwError "unknown quotient_def"

def of_type_spec (name: Ident) (sig: Option Ident): TSyntax `type_spec → CoreM (List Command)
  | `(type_spec| as $t:type .) => do
      .singleton <$> `(def $name $(sig.toArray)* := $(← of_type t))
  | `(type_spec| $id:inductive_def) => of_inductive_def name id
  | `(type_spec| $qd:quotient_def) => of_quotient_def name qd
  | _ => throwError "unknown type_spec"

def of_type_def : TSyntax ``type_def → CoreM (List Command)
  | `(type_def| The type $id_sig:id_sig $[( the $n1:ident $n2:ident ?)]?
                is defined $ts:type_spec) => do
      let (name, sig) ← of_id_sig id_sig
      let commands ← of_type_spec name sig ts
      let att ← n1.mapM (fun n1 =>
        let t := idents_to_nat_type n1 (n2.get!)
        `(attribute [natural_name $(mkStrLit t)] $name:ident)
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

def parse_def_eq : Term → CoreM (Term × String × Term × Term)
  | `($l = $r)
  | `($l ↔ $r) => do
      let (a, op, b) ← parse_infix l
      pure (a, map_op op, b, r)
  | _ => throwError "equation expected"

def eq_to_alt_expr (op: String) (fname: Ident) (t: Term): CoreM (TSyntax ``matchAltExpr) := do
  let (a, op', b, r) ← parse_def_eq t
  if op == op' then
    `(matchAltExpr| | $a, $b => $(replace_infix op fname r))
  else throwError "wrong infix op"

partial def pattern_type (args: LocalEnv) : Term → CoreM Term :=
  let rec f : Term → CoreM Term
    | `($x:ident) =>
        (args.lookup x.getId).getDM (throwError "undefined variable in pattern")
    | `(($t, $u)) => do `($(← f t) × $(← f u))
    | _ => throwError "unrecognized pattern in definition"
  f

partial def flat_name : Term → CoreM String
  | `($i:ident) => pure i.getId.toString
  | `($t × $u) => do pure $ (← flat_name t) ++ "_" ++ (← flat_name u)
  | _ => throwError "flat_name: can't encode"

partial def embed_name (type: Term) (name: Name) : CoreM Ident := match type with
  | `($i:ident) => pure $ mkIdent (i.getId ++ name)
  | `($t $_u) => embed_name t name
  | _ => do pure $ mkIdent $ Name.mkSimple ((← flat_name type) ++ "_" ++ name.toString)

partial def subst_base (t: Term) : Term → CoreM Term
  | `($u $v) => do `($(← subst_base t u) $v)
  | _ => pure t

def is_application : Term → Bool
  | `($_ $_) => true
  | _ => false

def op_def_commands (op: String) (op_name: Name) (args: List (Name × Term)) (eqs: List Term)
    (justification: Option Ident) : CoreM (List Command × Term × Ident) := do
  match eqs with
    | [eq] =>
        let (x, _op, y, r) ← parse_def_eq eq
        let (x, y) := if op == "∈" then (y, x) else (x, y)
        match x, y with
          | `(show $qx:ident from Quotient.mk _ $x), `(show $qy:ident from Quotient.mk _ $y) => do
              -- implicit function definition on quotient type
              let target_type := qx
              let aux_name ← embed_name target_type (op_name ++ `aux)
              let (tx, ty) ← mapM_pair (pattern_type args) (x, y)
              let aux ← `(def $aux_name | ($x : $tx), ($y : $ty) => $r)
              let by_thms ← proof_by_multi (mkIdent ``Quotient.sound :: justification.toList)
              let fname ← embed_name target_type op_name
              let d ← `(def $fname (a: $qx) (b: $qy) : $qx :=
                Quotient.lift₂ $aux_name $by_thms a b)
              pure ([aux, d], target_type, fname)
          | _, _ =>  -- direct function definition
              let (tx, ty) ← mapM_pair (pattern_type args) (x, y)
              let fname ← embed_name tx op_name
              let d ← match x, y with
                | `($x:ident), `($y:ident) => `(def $fname ($x : $tx) ($y : $ty) := $r)
                | _, _ => `(def $fname | ($x : $tx), ($y : $ty) => $r)
              pure ([d], ⟨tx⟩, fname)
    | eq :: _ => do  -- recursive function definition by cases
        let (x, _, _, _) ← parse_def_eq eq
        let target_type ← pattern_type args x
        let fname ← embed_name target_type op_name
        let alts ← eqs.mapM (eq_to_alt_expr op fname)
        let c ← `(set_option linter.unusedVariables false in
          def $fname : $target_type → $target_type → $target_type
            $(alts.toArray):matchAlt*)
        pure ([c], target_type, fname)
    | _ => throwError "equation expected"

def generate_op_def (op: String) (args: List (Name × Term)) (eqs: List Term)
    (justification: Option Ident) : CoreM (List Command) := do
  let (op_name, cl) ← (op_class.lookup op).getDM $ throwError "generate_def: no op"
  let eqs ← eqs.mapM (resolve_term args)
  let (def_cmds, target_type, fname) ← op_def_commands op op_name args eqs justification

  let instName ← embed_name target_type (Name.mkSimple ("inst" ++ cl.toString))

  -- If the target type is polymorphic (e.g. Set α), make the type class polymorphic
  -- similarly (e.g. Membership α).
  let type_class ← subst_base (mkIdent cl) target_type

  let grind_attribute := !(is_application target_type)  -- only add for monomorphic type
  let attr ← if grind_attribute then .some <$> `(attributes| @[method_specs])
                                else pure none

  -- Declare that the function we defined implements the operator (op).
  let i ← `(
    $attr:attributes ?
    instance $instName:ident : $type_class $(⟨target_type⟩) where
      $(mkIdent op_name):ident := $fname
  )

  -- Optionally add an attribute for grind.
  let g ← if grind_attribute then
    let spec := instName.getId ++ Name.mkSimple (op_name.toString ++ "_spec")
    some <$> `(attribute [grind =] $(mkIdent spec))
  else pure none

  let m ←
    if op == "*" then (as_ident target_type).bindM (fun i => `(attribute [implicit_mul] $i))
  else pure none

  pure (def_cmds ++ [i] ++ g.toList ++ m.toList)

def infer_type : TSyntax `expr → CoreM Term
  | `(expr| $t:ident [ $_:expr ]) => pure t
  | _ => throwError "must specify constant type"

def of_direct_def : TSyntax `direct_def → CoreM (List Command)
  | `(direct_def| $_:_for_all $ids_type:ids_types , $p:prop . $just:justification ?) => do
      let args ← of_ids_types ids_type
      let eq ← of_prop p
      let (_, op, _, _) ← parse_def_eq eq
      generate_op_def op (map_fst TSyntax.getId args) [eq] (← just.mapM of_justification)
  | `(direct_def| $n:num $[: $type:type]? = $e:expr .) => do
      let expr ← of_expr e >>= resolve_term []
      let type ← type.elim (infer_type e) of_type
      pure [← nat_instance type n expr]
  | _ => throwError "unknown direct_def"

def of_cases_def : TSyntax ``cases_def → CoreM (List Command)
  | `(cases_def| The $_:_operator $op:binary_op on $_type:ident is defined recursively
                    such that for all $ids_type:ids_types , $items:prop_item*) => do
      let args ← of_ids_types ids_type
      let eqs ← .map ThmDecl.thm <$> items.toList.mapM of_prop_item
      generate_op_def (of_binary_op op) (map_fst TSyntax.getId args) eqs none
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
                      on $type:type . $pn:post_name) => withRef body do
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

def of_top_decl : TSyntax `top_decl → CoreM (List Command × List Ident × Bool)
  | `(top_decl| Definition . $d) => (·, [], false) <$> of_definition d
  | `(top_decl| $_:_thm $t:_theorem) => do
    let (cmds, names) ← of_theorem [] t
    pure (cmds, names, true)
  | _ => throwError "unknown top_decl"

elab t:top : command => do
  let cs : Command ← liftCoreM $ command_set =<< match t with
    | `(top| $d:top_decl $[Corollary $ts:_theorem]*) => do
        let (commands, names, is_thm) ← of_top_decl d
        let corrs ← List.map (·.1) <$> ts.toList.mapM (fun c => withRef c.raw do
          if is_thm && names == []
            then throwError "unnamed theorem may not have a corollary"
            else of_theorem names c)
        pure $ commands ++ corrs.flatten
    | _ => throwError "unknown top"
  elabCommand cs
