import Natural.Proof

open Lean
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Parser.Command
open Lean.Parser.Term
open Lean.Syntax

namespace Natural

-- notation

def of_notation_decl: TSyntax ``notation_decl → CoreM (List Command)
  | `(notation_decl| Notation . $op:str is $_:_a $kind:op_kind operator . [ $i:ident ]) => do
      match i.getId.components with
        | [ type, fn ] => do
            let k := of_op_kind kind
            let s ← if k == .postfix && is_super_letter op.getString
              then pure []  -- looks like exponentation, so no need for syntax rule
              else .singleton <$> match of_op_kind kind with
                | .infix => `(syntax expr $op:str expr : expr)
                | .prefix => `(syntax $op:str expr : expr)
                | .postfix => `(syntax expr $op:str : expr)

            let ns ← getCurrNamespace
            let a ← `(attribute [natural_op $op $(mkIdent ns) $(mkIdent fn) $kind]
                                $(mkIdent type))
            pure (s ++ [a])
        | _ => throwError "notation: expected type.name"
  | _ => throwError "unknown notation_decl"

-- definitions

def of_label: TSyntax ``label → CoreM Name
  | `(label| $i:ident) => pure i.getId
  | _ => throwError "unknown label"

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
  let op_expr ← build_infix (← `(x)) (of_binary_op op) (← `(y))
  `(fun x y : $type => $op_expr)

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
      let inst_name := id_append name `Setoid
      let inst_cmd ← `(instance $inst_name:ident : Setoid ($type) where
        r := $(← op_fun op type)
        iseqv := $(← proof_by (.some (← of_justification j))))
      let quot_cmd ← `(def $name := Quotient ($inst_name))
      let mk_quot := id_append name `mk_quot
      let mk_cmd ← `(abbrev $mk_quot (x : $type) : $name := Quotient.mk _ x)
      let exact_thm ← `(
        @[grind =]
        theorem $(id_append name `exact) :
          ∀ x y : $type, $mk_quot x = $mk_quot y ↔ x ≈ y :=
            by default_apply Quotient.exact Quotient.sound)
      pure [inst_cmd, quot_cmd, mk_cmd, exact_thm]
  | _ => throwError "unknown quotient_def"

def of_type_spec (name: Ident) (sig: Option Ident): TSyntax `type_spec → CoreM (List Command)
  | `(type_spec| as $t:type .) => do
      -- Explicitly mark a type argument as having type (Type _).  Without this we'll get
      -- a constructor type with a max universe expression, which can cause trouble when
      -- we declare type class instances.
      let sig ← sig.mapM (fun id => `(bracketedBinder| ($id : Type _)))
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
  | `(top_sentence| $[Then]? $p:prop . $pn:post_name) => do
      pure (← of_prop p, ← of_post_name pn)
  | _ => throwError "unknown top_sentence"

def of_init_sentence : TSyntax ``init_sentence → CoreM (List ProofStep)
  | `(init_sentence| $iss:init_step /* .) =>
      iss.getElems.toList.mapM of_init_step
  | _ => throwError "unknown init_sentence"

def of_init_steps (env: BinderEnv): TSyntax ``init_steps → CoreM (List ProofStep)
  | `(init_steps| $iss:init_sentence*) =>
      iss.toList.flatMapM of_init_sentence >>= with_implicit_let env
  | _ => throwError "unknown init_steps"

partial def pattern_type (args: LocalEnv) : Term → CoreM Term :=
  let rec f : Term → CoreM Term
    | `($x:ident) =>
        (args.lookup x.getId).getDM (throwError s!"undefined variable '{x.getId}' in pattern")
    | `(($t, $u)) => do `($(← f t) × $(← f u))
    | _ => throwError "unrecognized pattern in definition"
  f

partial def flat_name : Term → CoreM String
  | `($i:ident) => pure i.getId.toString
  | `($t × $u) => do pure $ (← flat_name t) ++ "_" ++ (← flat_name u)
  | _ => throwError "flat_name: can't encode"

partial def embed_name (type: Term) (name: Name) : CoreM Ident := match type with
  | `($i:ident) => pure $ id_append i name
  | `($t $_u) => embed_name t name
  | `($_ → $_) => pure $ mkIdent (`Function ++ name)
  | _ => do pure $ mkIdent $ Name.mkSimple ((← flat_name type) ++ "_" ++ name.toString)

partial def subst_base (t: Term) : Term → CoreM Term
  | `($u $v) => do `($(← subst_base t u) $v)
  | _ => pure t

def is_application : Term → Bool
  | `($_ $_) => true
  | _ => false

def is_implicit_quotient (x: Term) (y: Term): Option (Ident × Term × Term) :=
  match x, y with
    | `($f:ident $x), `($g:ident $y) =>
      match f.getId.components, g.getId.components with
        | [t, `mk_quot], [_t', `mk_quot] => .some (mkIdent t, x, y)
        | _, _ => .none
    | _, _ => .none

def is_mkquot : Term → Option (Ident × Term)
    | `($f:ident $x) =>
      match f.getId.components with
        | [q, `mk_quot] => .some (mkIdent q, x)
        | _  => .none
    | _ => .none

def rm_mkquot (t: Term): CoreM Term := match is_mkquot t with
  | .some (_, t) => pure t
  | .none => throwError "expected quotient projection"

def DefEq := List Term × Term

def def_pat_command (name: Ident) (arg_types: List Term) (eqs: List DefEq)
                    (attr: Option (TSyntax `Lean.Parser.Term.attributes)) : CoreM Command := do
  let alt | (args, r) => do
    let args ← args.zipWithM (fun arg type => `( ($arg : $type) )) arg_types
    `(matchAltExpr| | $(args.toArray),* => $r)
  let alts ← eqs.mapM alt
  let d ← `($attr:attributes ? def $name $(alts.toArray):matchAlt*)
  if eqs.length > 1 then `(set_option linter.unusedVariables false in $d:command) else pure d

def def_command (name: Ident) (arg_types: List Term) (eqs: List DefEq)
                (attr: Option (TSyntax `Lean.Parser.Term.attributes)) : CoreM Command :=
  match eqs with
    | [(args, r)] => do
        if args.all (fun t => t.raw.isIdent) then
          let args ← binders ((args.map as_ident!).zip arg_types)
          `($attr:attributes ? def $name $args* := $r)
        else def_pat_command name arg_types eqs attr
    | _ => def_pat_command name arg_types eqs attr

def swap_args : List α → List α
  | [x, y] => [y, x]
  | _ => panic! "swap_args"

def def_inst_commands (op_name: Name) (type: Term) (fname: Ident) (cl: Name)
      : CoreM (List Command) := do
  let instName ← embed_name type (Name.mkSimple ("inst" ++ cl.toString))

  let t := (← global_type cl).get!
  let poly := t.getNumHeadForalls > 1  -- true if type class is polymorphic
  let type_class ← if poly then
      subst_base (mkIdent cl) type  -- use type argument(s) matching the target type
    else pure $ mkIdent cl

  let grind_attribute := !poly  -- only add for monomorphic type
  let attr ← if grind_attribute then .some <$> `(attributes| @[method_specs])
                                else pure none

  -- Declare that the function we defined implements the operator (op).
  let impl_cmd ← `(
    $attr:attributes ?
    instance $instName:ident : $type_class $(⟨type⟩) where
      $(mkIdent op_name):ident := $fname
  )

  -- Optionally add an attribute for grind.
  let g ← if grind_attribute then
    let spec := instName.getId ++ Name.mkSimple (op_name.toString ++ "_spec")
    some <$> `(attribute [grind =] $(mkIdent spec))
  else pure none

  pure $ [impl_cmd] ++ g.toList

def declare_op (info: OpInfo): CoreM (Option Command) :=
  info.type.mapM (fun type =>
      let name := Lean.Syntax.mkStrLit info.name
      let fn := mkIdent (type ++ info.fname)
      match info.kind with
        | .infix => `(infix:1024 $name:str => $fn)
        | .prefix => `(prefix:1024 $name:str => $fn)
        | .postfix => `(postfix:1024 $name:str => $fn)
  )

def is_op (s: String) := !s.front.isAlpha

def generate_def (decl_fn: Option String) (env: BinderEnv) (eqs: List (String × DefEq))
    (justification: Option Ident) : TermElabM (List Command) := do
  let env ← env.mapM (check_no_binder_op ·)
  let eqs ← eqs.mapM (fun (fn, args, r) => do
    pure $ (fn, ← args.mapM (resolve_left ·.raw), ← resolve_term env r))
  let (fns, defeqs) := eqs.unzip
  let fn := fns.head!
  if !decl_fn.all (· == fn) then throwError "declaration mismatch"
  let op_info ← if is_op fn
    then do pure $ some $ ← (← lookup_op fn).getDM (throwError "unknown op")
    else pure none
  let fname := op_info.elim (Name.mkSimple fn) (·.fname)

  let defeqs := if fn == "∈" then map_fst swap_args defeqs else defeqs
  let arg1 ← match defeqs with
    | (arg :: _, _) :: _ => pure arg
    | _ => throwError "generate_def: no arg"

  let (is_quotient, arg_type, dname, defeqs) ← match is_mkquot arg1 with
    | .some (qtype, _) =>
        let defeqs ← mapM_fst (List.mapM (rm_mkquot ·)) defeqs  -- remove projections
        pure (true, as_term qtype, fname ++ `aux, defeqs)
    | .none => do
        pure (false, ← pattern_type env arg1, fname, defeqs)

  let args_types ← match defeqs with
    | [(ts, _)] => ts.mapM (pattern_type env ·)
    | (ts, _) :: _ => pure $ ts.map (fun _ => arg_type)
    | _ => throwError "generate_def: no arg"

  let def_name ← embed_name arg_type dname
  let top_name ← embed_name arg_type fname

  let defeqs := if is_quotient then defeqs else map_snd (replace_op fn top_name) defeqs
  let attr ← if op_info.all (fun i => i.type.isSome)
    then .some <$> `(attributes| @[grind]) else pure none
  let def_cmd ← def_command def_name args_types defeqs attr

  let lift_cmd ← if is_quotient then List.singleton <$> do
    let by_thms ← proof_by_multi (mkIdent ``Quotient.sound :: justification.toList)
    `(def $top_name (a: $arg_type) (b: $arg_type) : $arg_type :=
        Quotient.lift₂ $def_name $by_thms a b)
  else pure []

  let op_def_command ← op_info.bindM (declare_op ·)
  let inst_commands ←
    (op_info.bind (·.cls)).toList.flatMapM
      (def_inst_commands fname arg_type top_name ·)

  let nat_decl ← if is_op fn then pure none
    else some <$> `(attribute [natural_name $(mkStrLit fn)] $top_name)

  pure ([def_cmd] ++ lift_cmd ++ op_def_command.toList ++ inst_commands ++ nat_decl.toList)

def infer_type : TSyntax `expr → CoreM Term
  | `(expr| $t:ident [ $_:expr ]) => pure t
  | _ => throwError "must specify constant type"

def of_def_eq : TSyntax `def_eq → CoreM (String × DefEq)
  | `(def_eq| $l:expr = $r:expr) => do
      let (l, r) ← mapM_pair of_expr (l, r)
      let (op, args) ← match l with
        | `(_super $e $s $id:ident) =>  -- either exponentiation or a postfix op
            let id := id.getId.toString (escape := false)
            if (← lookup_op id).any (fun info => info.kind == .postfix)
              then pure (id, [e]) else pure ("^", [e, s])
        | _ => parse_op l
      pure (map_op op, args, ⟨r.raw⟩)
  | `(def_eq| $e:expr $op:rel_op $f:expr $_:_iff $r:prop) => do
      pure (of_binary_op op, [← of_expr e, ← of_expr f], ← of_prop r)
  | `(def_eq| $e:expr is $i:ident $_:_iff $r:prop) => do
      pure (i.getId.toString, [← of_expr e], ← of_prop r)
  | _ => throwError "unknown def_eq"

def of_direct_def : TSyntax `direct_def → TermElabM (List Command)
  | `(direct_def| $[$ls:let_step .]* $ids:for_all_ids ? $eq:def_eq . $just:justification ?) => do
      let ls ← ls.toList.mapM (of_let_step ·)
      let vars ← ids.toList.flatMapM (of_for_all_ids ·)
      let eq ← of_def_eq eq
      let args := lets_vars ls ++ map_fst TSyntax.getId vars
      generate_def none args [eq] (← just.mapM (of_justification ·))
  | `(direct_def| $n:num $[: $type:type]? = $e:expr .) => do
      let expr ← of_expr e >>= resolve_term []
      let type ← type.elim (infer_type e) (of_type ·)
      pure [← nat_instance type n expr]
  | _ => throwError "unknown direct_def"

def of_cases_def : TSyntax ``cases_def → TermElabM (List Command)
  | `(cases_def|
        The $_:_operator $op:binary_op on $_type:ident is defined recursively
        such that $ids:for_all_ids $[$_:label . $eqs:def_eq .]*) => do
      let args ← of_for_all_ids ids
      let eqs ← eqs.toList.mapM (of_def_eq ·)
      generate_def (some (of_binary_op op)) (map_fst TSyntax.getId args) eqs none
  | _ => throwError "unknown cases_def"

def of_definition : TSyntax `definition → TermElabM (List Command)
  | `(definition| $d:type_def) => of_type_def d
  | `(definition| $d:direct_def) => of_direct_def d
  | `(definition| $e:cases_def) => of_cases_def e
  | _ => throwError "unknown definition"

-- theorems

abbrev Label := Name

structure ThmDecl where
  label: Option Label
  init_steps: List ProofStep
  thm: Term
  name: Option Ident
  attr: Option Ident

def of_prop_item (env: BinderEnv) : TSyntax ``prop_item → CoreM ThmDecl
  | `(prop_item| $i:label . $iss:init_steps $s:top_sentence) => withRef s do
      let iss ← of_init_steps env iss
      let (thm, name, attr) ← of_top_sentence s
      pure ⟨← of_label i, iss, ← apply_init_steps iss thm, name, attr⟩
  | _ => throwError "unknown prop_item"

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

def match_proofs : List ThmDecl → List (Label × _Proof) → CoreM (List (ThmDecl × Option _Proof))
  | [], [] => pure []
  | decl :: ts, (j, proof) :: ps =>
      if decl.label == j then .cons (decl, .some proof) <$> match_proofs ts ps
      else .cons (decl, .none) <$> match_proofs ts ((j, proof) :: ps)
  | decl :: ts, [] => .cons (decl, .none) <$> match_proofs ts []
  | [], (j, _) :: _ => throwError s!"unmatched proof label: {j}"

def translate_proofs (init_steps: List ProofStep) (thms_proofs: List (ThmDecl × Option _Proof))
    : TermElabM (List (ThmDecl × Option Term)) :=
  thms_proofs.mapM (fun (decl, proof) => withRef decl.thm do
    let thm ← resolve_term1 (lets_vars init_steps) decl.thm
    pure ({decl with thm := ← generalize init_steps thm},
          ← proof.mapM (translate_proof (init_steps ++ decl.init_steps) thm)))

def of_props_proofs (init_steps: List ProofStep) (ps: TSyntax `props_proofs) :
        TermElabM (List (ThmDecl × Option Term)) :=
  match ps with
    | `(props_proofs| $s:top_sentence $[ $_:_proof_dot $proof:proof ]?) => do
        let (thm, opt_name, opt_attr) ← of_top_sentence s
        let decl := ThmDecl.mk none [] thm opt_name opt_attr
        translate_proofs init_steps [(decl, ← proof.mapM (of_proof ·))]
    | `(props_proofs| $ps:prop_item* $[ $_:_proof_dot $pis:proof_items ]?) => do
        let env := lets_vars init_steps
        let label_thms ← ps.toList.mapM (of_prop_item env ·)
        let label_proofs := (← pis.mapM (of_proof_items ·)).getD []
        let thms_proofs ← match_proofs label_thms label_proofs
        translate_proofs init_steps thms_proofs
    | _ => throwError "unknown prop_or_items"

def mk_decl (is_instance: Bool) (attr: Option Ident) (name: Option Ident)
            (thm proof: Term) : CoreM Command := do
  let a ← attr.mapM (fun a => `(attributes| @[$a:ident]))
  if is_instance then `($a:attributes ? instance $[$name:ident]? : $thm := $proof)
  else match name with
    | Option.some name => `($a:attributes ? theorem $name : $thm := $proof)
    | Option.none => `($a:attributes ? example : $thm := $proof)

def of_theorem_body (name: Option Ident) (corollary_of: List Ident)
          (body: TSyntax `theorem_body) : TermElabM (List Command × List Ident) := do
  let by_default : Option Ident := match corollary_of with
    | [c] => Option.some c  -- use corollary_of by default if there is just one
    | _ => .none
  match body with
    | `(theorem_body| $iss:init_steps $ps:props_proofs) => do
        let thms_proofs ← of_props_proofs (← of_init_steps [] iss) ps
        let (commands, names) := List.unzip $ ← thms_proofs.mapM
          (fun (⟨label, _init_steps, thm, thm_name, attr⟩, proof) => withRef thm do
            let proof := proof.getD (← proof_by by_default)
            let name := thm_name <|> name.map (fun name =>
              label.elim name (mkIdent $ name.getId ++ ·))
            let command ← mk_decl false attr name thm proof
            pure (command, name))
        pure (commands, (names.flatMap Option.toList))
    | `(theorem_body| The $_:_operator $op:binary_op is $_:_a ? $kind:natural_type
                      on $type:type . $pn:post_name) => withRef body do
        let env ← getEnv
        let kind ← match (← of_natural_type kind) with
          | `($kind:ident) => pure kind  -- name of type class or structure
          | _ => throwError "id expected"
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
            : TSyntax ``_theorem → TermElabM (List Command × List Ident)
    | `(_theorem| $name:thm_name ? $_:str ? . $b:theorem_body) => do
        let name ← name.mapM (of_thm_name ·)
        of_theorem_body name corollary_of b
    | _ => throwError "unknown theorem"

def of_thm_or_def : TSyntax `thm_or_def → TermElabM (List Command × List Ident × Bool)
  | `(thm_or_def| Definition . $d) => (·, [], false) <$> of_definition d
  | `(thm_or_def| $_:_thm $t:_theorem) => do
    let (cmds, names) ← of_theorem [] t
    pure (cmds, names, true)
  | _ => throwError "unknown thm_or_def"

elab t:top : command => do
  let cs : Command ← liftTermElabM $ (command_set ·) =<< match t with
    | `(top| $n:notation_decl) => of_notation_decl n
    | `(top| $d:thm_or_def $[Corollary $ts:_theorem]*) => do
        let (commands, names, is_thm) ← of_thm_or_def d
        let corrs ← List.map (·.1) <$> ts.toList.mapM (fun c => withRef c.raw do
          if is_thm && names == []
            then throwError "unnamed theorem may not have a corollary"
            else of_theorem names c)
        pure $ commands ++ corrs.flatten
    | _ => throwError "unknown top"
  elabCommand cs
