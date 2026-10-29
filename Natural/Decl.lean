import Natural.Proof

open Lean
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Parser.Command
open Lean.Parser.Term
open Lean.Syntax

namespace Natural

-- notation

def of_op_decl (op: StrLit) (neg: Option StrLit) (kind: TSyntax ``op_kind)
               (rel: Bool) (i: Name) : CoreM (List Command) := do
  match i.components with
    | [ type, fn ] => do
        if neg.isSome && !rel then
          throwError "only a relational operator can have a negation"

        let k := of_op_kind kind
        let syntax_decl ← if k == .postfix && is_super_letter op.getString
          then pure []  -- looks like exponentation, so no need for syntax rule
          else
            if rel then
              let ops := op :: neg.toList
              ops.mapM (fun o => `(syntax $o:str : rel_op))
            else .singleton <$> match k with
              | .infix => `(syntax expr $op:str expr : expr)
              | .prefix => `(syntax $op:str expr : expr)
              | .postfix => `(syntax expr $op:str : expr)
              | .mixfix => throwError "of_op_decl: mixfix unexpected"
        let op_decl ← `(syntax $op:str : op)

        let ns ← getCurrNamespace
        let prec := Syntax.mkNumLit (if rel then 50 else 100).repr
        let target := if type == `Type then ``TypeDummy else type
        let a ← `(attribute [natural_op $op $[$neg]? $(mkIdent ns) $(mkIdent fn) $kind $prec]
                            $(mkIdent target))
        pure (syntax_decl ++ [op_decl, a])
    | _ => throwError "of_op_decl: expected type.name"

def of_mixfix_decl (ts: TSyntaxArray `mixfix_token) (cat: Ident) (id: Name)
        : CoreM (List Command) :=
  match id.components with
    | [ type, fn ] => do
        let tokens ← ts.toList.mapM of_mixfix_token
        let es ← tokens.mapM (fun
          | .str s => `(stx| $(Lean.Syntax.mkStrLit s):str)
          | .ident _ => `(stx| expr))
        let es ← (·.toArray) <$> match tokens.head?, tokens.getLast? with
          | .some (.str first), .some (.str last) => do
              if first == last then
                -- If the first and last tokens are the same string, wrap the first
                -- two syntax items in 'atomic'.  This is helpful e.g. if the user
                -- defines the absolute value notation |x|.
                let (init, rest) := es.splitAt 2
                `(stx| atomic($[$(init.toArray):stx]*)) <&> (· :: rest)
              else pure es
          | _, _ => pure es
        let ns ← getCurrNamespace
        let name := mkIdent fn
        let str_name := Lean.Syntax.mkStrLit fn.toString
        let syntax_decl ← `(syntax (name := $name) $[$es:stx]* : $cat)
        let attr_decl ← `(attribute [natural_op
          $str_name $(.none)? $(mkIdent ns) $name mixfix 0 $ts*] $(mkIdent type))
        pure [syntax_decl, attr_decl]
    | _ => throwError "of_mixfix_decl: expected type.name"

def of_notation_decl: TSyntax ``notation_decl → CoreM (List Command)
  | `(notation_decl| $op:str $[(negation: $neg)]? is $_:_a
          $kind:op_kind $[$rel:relational]? operator . [ $i:ident ]) =>
      of_op_decl op neg kind rel.isSome i.getId
  | `(notation_decl| $ts:mixfix_token* is a $p:_propositional ?
                     mixfix notation . [ $i:ident ]) => do
      let cat := mkIdent (if p.isSome then `mixfix_prop else `mixfix_expr)
      of_mixfix_decl ts cat i.getId
  | _ => throwError "unknown notation_decl"

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

def op_fun (op: TSyntax α) (type: Term) : CoreM Term := do
  let op_expr ← build_infix (← `(x)) (of_op op) (← `(y))
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
  | `(quotient_def| as the quotient $t:simple_type / $op:rel_op .
                    $j:justification) => do
      let type ← of_simple_type t
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

def of_defined_term : TSyntax ``defined_term → CoreM String
  | `(defined_term| $i:ident $j:ident ?) => pure $ singular_name i j
  | _ => throwError "unknown defined_term"

def of_type_def : TSyntax ``type_def → CoreM (List Command)
  | `(type_def|
        The type $id_sig:id_sig $[($_:a_or_the $n:defined_term)]?
        is defined $ts:type_spec) => do
      let (name, sig) ← of_id_sig id_sig
      let commands ← of_type_spec name sig ts
      let att ← n.mapM (fun n1 => do
        let t ← of_defined_term n1
        `(attribute [natural type $(mkStrLit t):str] $name:ident)
      )
      pure $ commands ++ att.toList
  | _ => throwError "unknown definition"

def of_attrib: TSyntax ``attrib → CoreM (TSyntax ``attributes)
  | `(attrib| $a:attributes) => pure a
  | `(attrib| @ $i:ident) => `(attributes| @[$i:ident])
  | _ => throwError "unknown attrib"

def of_post_name : TSyntax ``post_name →
        CoreM (Option Ident × Option (TSyntax ``attributes))
  | `(post_name| $[ [ $i:thm_name $[ : $a:attrib ]? ] ]? ) => do
      pure (← i.mapM of_thm_name, ← a.join.mapM of_attrib)
  | _ => throwError "unknown post_name"

def of_top_sentence : TSyntax ``top_sentence →
        CoreM (Term × Option Ident × Option (TSyntax ``attributes))
  | `(top_sentence| $[Then]? $p:prop . $pn:post_name) => do
      pure (← of_prop p, ← of_post_name pn)
  | _ => throwError "unknown top_sentence"

def of_init_sentence : TSyntax ``init_sentence → CoreM (List ProofStep)
  | `(init_sentence| $iss:init_step /* .) =>
      iss.getElems.toList.mapM of_init_step
  | _ => throwError "unknown init_sentence"

def of_init_steps : TSyntax ``init_steps → CoreM (List ProofStep)
  | `(init_steps| $iss:init_sentence*) => iss.toList.flatMapM of_init_sentence
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

partial def base_name : Term → Option Name
  | `($i:ident) => some i.getId
  | `(Type) => some `Type
  | `($_ → $_) => some `Function
  | `($t $_) => base_name t
  | _ => none

partial def embed_name (type: Term) (name: Name) : CoreM Ident :=
  if let some t := base_name type then pure $ mkIdent (t ++ name)
  else do pure $ mkIdent $ Name.mkSimple ((← flat_name type) ++ "_" ++ name.toString)

partial def subst_base (t: Term) : Term → CoreM Term
  | `($u $v) => do `($(← subst_base t u) $v)
  | _ => pure t

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

structure DefEq where
  name: String    -- operator (e.g. "+"), mixfix kind or natural-language name
  kind: Option OpKind
  cat: Option Category
  args: List Term
  val: Term
deriving Inhabited

def def_pat_command (name: Ident) (arg_types: List Term) (eqs: List DefEq)
                    (attr: Option (TSyntax `Lean.Parser.Term.attributes)) : CoreM Command := do
  let alt (eq: DefEq) := do
    let args ← eq.args.zipWithM (fun arg type => `( ($arg : $type) )) arg_types
    `(matchAltExpr| | $(args.toArray),* => $eq.val)
  let alts ← eqs.mapM alt
  let d ← `($attr:attributes ? def $name $(alts.toArray):matchAlt*)
  if eqs.length > 1 then `(set_option linter.unusedVariables false in $d:command) else pure d

def def_command (name: Ident) (arg_types: List Term) (eqs: List DefEq)
                (attr: Option (TSyntax `Lean.Parser.Term.attributes)) : CoreM Command :=
  match eqs with
    | [eq] => do
        if eq.args.all (fun t => t.raw.isIdent) then
          let args ← binders ((eq.args.map as_ident!).zip arg_types)
          `($attr:attributes ? def $name $args* := $eq.val)
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

def declare_op (info: OpInfo): CoreM (List Command) :=
  info.type.toList.flatMapM (fun type =>
    let name := Lean.Syntax.mkStrLit info.name
    let fn := mkIdent (type ++ info.fname)
    let prec := mkNumLit info.prec.repr
    let decl := match info.kind with
      | .infix => `(infix:$prec $name:str => $fn)
      | .prefix => `(prefix:$prec $name:str => $fn)
      | .postfix => `(postfix:$prec $name:str => $fn)
      | .mixfix => do
          let ts := info.tokens.toArray
          let ns ← ts.mapM (fun
            | .str s => `(notationItem| $(Lean.Syntax.mkStrLit s):str)
            | .ident i => `(notationItem| $(mkIdent i):ident))
          let args := ts.filterMap (fun
            | .str _ => .none
            | .ident i => .some (mkIdent i))
          `(notation $[$ns:notationItem]* => $(Syntax.mkApp fn args))
    let neg_decl := info.neg.map (fun neg => do
      let neg := Lean.Syntax.mkStrLit neg
      let op_expr ← build_infix (← `(x)) info.name (← `(y))
      `(infix:$prec $neg:str => fun x y => ¬ $op_expr))
    sequence (decl :: neg_decl.toList)
  )

def quotient_lift (top_name: Ident) (def_name: Ident) (n: Nat) (arg_type: Term)
      (justification: Option Ident) : CoreM Command := do
  let by_thms ← proof_by_multi (mkIdent ``Quotient.sound :: justification.toList)
  let (q, type) ← match n with
    | 1 => pure (``Quotient.lift, ← `($arg_type → $arg_type))
    | 2 => pure (``Quotient.lift₂, ← `($arg_type → $arg_type → $arg_type))
    | _ => throwError "unsupported lift"
  `(def $top_name : $type := $(mkIdent q) $def_name $by_thms)

def generate_def (decl_fn: Option String) (arg_type: Option Term)
    (env: Vars) (defeqs: List DefEq)
    (justification: Option Ident) : TermElabM (List Command) := do
  let env ← env.mapM (check_no_binder_op ·)
  let defeqs ← defeqs.mapM (fun (d : DefEq) => do
    pure $ { d with args := ← d.args.mapM (resolve_left ·.raw),
                    val := ← resolve_term env d.val })
  let { name := fn, kind, cat, args, .. } := defeqs.head!
  if !decl_fn.all (· == fn) then throwError "declaration mismatch"
  let op_info ← kind.mapM (fun kind => do
    (← lookup_op fn kind).getDM (throwError "unknown op"))
  let fname := op_info.elim (Name.mkSimple (function_name fn)) (·.fname)

  let defeqs := if fn == "∈"
    then defeqs.map (fun d => { d with args := swap_args d.args }) else defeqs
  let arg1 ← match defeqs with
    | { args := arg :: _, .. } :: _ => pure arg
    | _ => throwError "generate_def: no arg"

  let (is_quotient, arg_type, dname, defeqs) ← match is_mkquot arg1 with
    | .some (qtype, _) =>
        let defeqs ← defeqs.mapM (fun d => do
          pure { d with args := ← d.args.mapM (rm_mkquot ·) })  -- remove projections
        pure (true, as_term qtype, fname ++ `aux, defeqs)
    | .none => do
        let arg_type ← arg_type.elim (pattern_type env arg1) pure
        pure (false, arg_type, fname, defeqs)

  if !(op_info.all (fun info => info.type.all (· == base_name arg_type)))
    then throwError f!"op type mismatch: {op_info.get!.type.get!} / {base_name arg_type} "

  let args_types ← match defeqs with
    | [{ args := ts, ..}] => ts.mapM (pattern_type env ·)
    | { args := ts, .. } :: _ => pure $ ts.map (fun _ => arg_type)
    | _ => throwError "generate_def: no arg"

  let (def_name, top_name) ←
    if (op_info.isSome || cat.isSome)
      then mapM_pair (embed_name arg_type ·) (dname, fname)
      else pure (mkIdent dname, mkIdent fname)

  let defeqs := if is_quotient then defeqs
    else defeqs.map (fun d => { d with val := replace_op fn top_name d.val })
  let attr ← if op_info.all (fun i => i.type.isSome)
    then .some <$> `(attributes| @[grind]) else pure none

  let def_cmd ← def_command def_name args_types defeqs attr

  let lift_cmd ← if is_quotient
    then .singleton <$> quotient_lift top_name def_name args.length arg_type justification
    else pure []

  let op_def_commands ← op_info.toList.flatMapM (declare_op ·)
  let inst_commands ←
    (op_info.bind (·.cls)).toList.flatMapM
      (def_inst_commands fname arg_type top_name ·)

  let nat_decl ← if op_info.isSome then pure none
    else cat.mapM (fun cat => do
      let cat ← to_category cat
      `(attribute [natural $cat $(mkStrLit fn):str] $top_name))

  pure ([def_cmd] ++ lift_cmd ++ op_def_commands ++ inst_commands ++ nat_decl.toList)

def infer_type : TSyntax `expr → CoreM Term
  | `(expr| $t:ident [ $_:expr ]) => pure t
  | _ => throwError "must specify constant type"

def elab_commands (commands: List Command) : CommandElabM Unit := do
  let ctrace cmd := do
    trace[natural] cmd
    pure ()
  commands.forM ctrace
  let command : Command := Lean.TSyntax.mk (mkNullNode commands.toArray)
  elabCommand command

def mixfix_defeq (mix: Syntax) (r: Term): CoreM DefEq := do
  let stx_kind := mix.getKind
  let args ← (mix.getArgs.toList.filter (! ·.isAtom)).mapM (of_expr ⟨·⟩)
  pure { name := stx_kind.toString, kind := OpKind.mixfix, cat := none,
          args, val := r }

def of_def_eq : TSyntax `def_eq → CoreM DefEq
  | `(def_eq| $l:expr = $r:expr) => do
      let (l, r) ← mapM_pair of_expr (l, r)
      let (op, kind, args) ← match ← resolve_left l with
        | `(_super $e $s $id:ident) =>  -- either exponentiation or a postfix op
            let id := id.getId.toString (escape := false)
            if (← lookup_op id .postfix).any (fun info => info.kind == .postfix)
              then pure (id, some .postfix, [e]) else pure ("^", some .infix, [e, s])
        | `($f:ident $arg) => pure (f.getId.toString, .none, [arg])
        | _ => parse_op l <&> fun (op, kind, args) => (op, .some kind, args)
      pure { name := map_op op, kind, cat := none, args, val := ⟨r.raw⟩}
  | `(def_eq| $e:expr $op:rel_op $f:expr $_:def_if $r:prop) => do
      pure { name := of_op op, kind := OpKind.infix, cat := none,
             args := [← of_expr e, ← of_expr f], val := ← of_prop r }
  | `(def_eq| $m:mixfix_expr = $e:expr) =>
        of_expr e >>= mixfix_defeq m
  | `(def_eq| $m:mixfix_prop $_:def_if $p:prop) =>
        of_prop p >>= mixfix_defeq m
  | `(def_eq| $e:expr is $i:defined_term $_:def_if $r:prop) => do
      pure { name := ← of_defined_term i, kind := none, cat := some .property,
             args := [← of_expr e], val := ← of_prop r }
  | `(def_eq| $e:expr is a $d:defined_term of $f:id_list $_:def_if $r:prop) => do
      let f : List Term := (← of_id_list f).map (⟨·.raw⟩)
      pure { name := ← of_defined_term d, kind := none, cat := some .attribute,
             args := (← of_expr e) :: f, val := ← of_prop r }
  | _ => throwError "unknown def_eq"

def of_def1 : TSyntax ``def1 → CoreM (IdVars × DefEq)
  | `(def1| $[$ids:for_all_ids ,]? $eq:def_eq .) => do
      pure $ (← ids.toList.flatMapM (of_for_all_ids ·), ← of_def_eq eq)
  | _ => throwError "unknown def1"

def of_defs : TSyntax `defs → CoreM (List (IdVars × DefEq) × Option Ident)
  | `(defs| $d:def1 $j:justification ?) => do
        pure $ ([← of_def1 d], ← j.mapM of_justification)
  | `(defs| $[$_:label . $ds:def1]*) => do
        pure (← ds.toList.mapM of_def1, none)
  | _ => throwError "unknown defs"

def of_direct_def : TSyntax `direct_def → TermElabM (List Command)
  | `(direct_def| $[$ls:let_step .]* $defs:defs) => do
      let ls ← ls.toList.mapM (of_let_step ·)
      let (defs, just) ← of_defs defs
      defs.flatMapM (fun (vars, eq) =>
        let args := lets_vars ls ++ map_fst TSyntax.getId vars
        generate_def none none args [eq] just)
  | `(direct_def| $n:num $[: $type:type]? = $e:expr .) => do
      let expr ← of_expr e >>= resolve_term []
      let type ← type.elim (infer_type e) (of_type ·)
      pure [← nat_instance type n expr]
  | _ => throwError "unknown direct_def"

def of_cases_def : TSyntax ``cases_def → TermElabM (List Command)
  | `(cases_def|
        The $_:_operator $op:op on $type:ident is defined recursively
        such that $ids:for_all_ids , $[$_:label . $eqs:def_eq .]*) => do
      let args ← of_for_all_ids ids
      let eqs ← eqs.toList.mapM (of_def_eq ·)
      generate_def (some (of_op op)) (some type) (map_fst TSyntax.getId args) eqs none
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
  attr: Option (TSyntax ``attributes)

def of_prop_item (env: Vars) : TSyntax ``prop_item → CoreM ThmDecl
  | `(prop_item| $i:label . $iss:init_steps $s:top_sentence) => withRef s do
      let iss ← of_init_steps iss
      let iss ← with_implicit_let (env.map (·.1)) iss
      let (thm, name, attr) ← of_top_sentence s
      pure ⟨← of_label i, iss, ← apply_init_steps iss thm, name, attr⟩
  | _ => throwError "unknown prop_item"

def label_range (i j: Name) : CoreM (List Name) :=
  match i.toString.toList, j.toString.toList with
    | [c], [d] => pure $ (c ...= d).toList.map (Name.mkSimple ∘ Char.toString)
    | _, _ => throwError "label must be a single letter"

def of_proof_item: TSyntax ``proof_item → CoreM (List (Name × _Proof))
  | `(proof_item| $l:proof_label $p:proof) => do
      let (i, j) ← of_proof_label l
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

def translate_proofs (outer_steps: List ProofStep) (thms_proofs: List (ThmDecl × Option _Proof))
    : TermElabM (List (ThmDecl × Option Term)) :=
  thms_proofs.mapM (fun (decl, proof) => withRef decl.thm do

    -- Pre-resolve the theorem before trimming steps because resolution may change
    -- its set of free variables (e.g. ab -> a, b).
    let thm ← resolve_term1 (lets_vars outer_steps) decl.thm
    let outer_steps := trim_steps thm outer_steps

    -- Apply the trimmed steps, then resolve the entire theorem because the
    -- the steps themselves may contain assumptions that need resolution.
    let thm ← apply_init_steps outer_steps decl.thm >>= resolve_term1 []

    pure ({decl with thm},
          ← proof.mapM (translate_proof (outer_steps ++ decl.init_steps) thm)))

def of_props_proofs (outer_steps: List ProofStep) (ps: TSyntax `props_proofs) :
        TermElabM (List (ThmDecl × Option Term)) :=
  match ps with
    | `(props_proofs| $s:top_sentence $[ $_:_proof_dot $proof:proof ]?) => do
        let (thm, opt_name, opt_attr) ← of_top_sentence s
        let decl := ThmDecl.mk none [] thm opt_name opt_attr
        translate_proofs outer_steps [(decl, ← proof.mapM (of_proof ·))]
    | `(props_proofs| $ps:prop_item* $[ $_:_proof_dot $pis:proof_items ]?) => do
        let env := lets_vars outer_steps
        let label_thms : List ThmDecl ← ps.toList.mapM (of_prop_item env ·)
        let label_proofs : List (Name × _Proof) := (← pis.mapM (of_proof_items ·)).getD []
        let thms_proofs ← match_proofs label_thms label_proofs
        translate_proofs outer_steps thms_proofs
    | _ => throwError "unknown prop_or_items"

def mk_decl (is_instance: Bool) (attr: Option (TSyntax ``attributes)) (name: Option Ident)
            (thm proof: Term) : CoreM Command := do
  if is_instance then `($attr:attributes ? instance $[$name:ident]? : $thm := $proof)
  else match name with
    | Option.some name => `($attr:attributes ? theorem $name : $thm := $proof)
    | Option.none => `($attr:attributes ? example : $thm := $proof)

def of_type_class_ref : TSyntax `type_class_ref → CoreM Ident
  | `(type_class_ref| $a:natural_property) => of_natural_name a
  | `(type_class_ref| $_:_a $n:natural_class) => of_natural_name n
  | _ => throwError "unknown type_class_ref"

partial def has_holds (s: Syntax): Option Syntax := match s with
  | `(_holds $_ $_) => .some s
  | _ => match s with
    | .node _ _ args => args.findSome? has_holds
    | _ => .none

partial def subst_holds (x: Ident) (aux: Ident) : Syntax → CoreM Syntax
  | `(_holds _ $z) => `($aux $z)
  | s@`(_holds $y:ident $z) => if x.getId == y.getId then `($aux $z)
      else throwErrorAt s
        f!"theorem is parameterized with '{id_str x}', so cannot hold for '{id_str y}'"
  | s => do match s with
    | .node info kind args => pure $ .node info kind (← args.mapM (subst_holds x aux))
    | _ => pure s

def aux_abbrev (aux: Ident) (thm: Term) : CoreM (Ident × Command) :=
  match match_binder thm.raw with
    | .some (.all, (x, .some (":", type)) :: vars, t) => do
        pure (x, ← `(abbrev $aux ($x : $type) := $(← mk_for_all vars t)))
    | _ => throwError "self-referential theorem must have universal quantifier"

def of_theorem_body (name: Option Ident) (corollary_of: List Ident)
          (body: TSyntax `theorem_body) : TermElabM (List Command × List Ident) := do
  let by_default : Option Ident := match corollary_of with
    | [c] => Option.some c  -- use corollary_of by default if there is just one
    | _ => .none
  match body with
    | `(theorem_body| $iss:init_steps $ps:props_proofs) => do
        let iss ← of_init_steps iss
        let iss ← with_implicit_let [] iss
        let thms_proofs : List (ThmDecl × Option Term) ← of_props_proofs iss ps
        let (commands, names) := List.unzip $ ← thms_proofs.flatMapM
          (fun (⟨label, _init_steps, thm, thm_name, attr⟩, proof) => withRef thm do
            let proof := proof.getD (← proof_by by_default)
            let name := thm_name <|> name.map (fun name =>
              label.elim name (mkIdent $ name.getId ++ ·))
            let (aux_cmd, proof) ← match has_holds proof with
              | .some h =>
                let name ← name.getDM (throwErrorAt h
                  "self-referential theorem must have a name")
                let aux := mkIdent (name.getId.appendBefore "_")
                let (x, c) ← aux_abbrev aux thm
                pure ([c], (⟨← subst_holds x aux proof⟩ : Term))
              | .none => pure ([], proof)
            let command ← mk_decl false attr name thm proof
            pure (aux_cmd.map (·, .none) ++ [(command, name)]))
        pure (commands, (names.flatMap Option.toList))
    | `(theorem_body| The $_:_operator $op:op is $kind:type_class_ref
                      on $type:type . $pn:post_name) => withRef body do
        let env ← getEnv
        let kind ← of_type_class_ref kind
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
  let cs : List Command ← liftTermElabM $ match t with
    | `(top| Notation . $n:notation_decl) => of_notation_decl n
    | `(top| $d:thm_or_def $[Corollary $ts:_theorem]*) => do
        let (commands, names, is_thm) ← of_thm_or_def d
        let corrs ← List.map (·.1) <$> ts.toList.mapM (fun c => withRef c.raw do
          if is_thm && names == []
            then throwError "unnamed theorem may not have a corollary"
            else of_theorem names c)
        pure $ commands ++ corrs.flatten
    | _ => throwError "unknown top"
  let c : Command := TSyntax.mk (mkNullNode cs.toArray)
  elabCommand c

  -- We trace only after elaborating because some commands could have syntax
  -- that is defined in previous commands in the same group.
  let ctrace cmd := do
    trace[natural] cmd
    pure ()
  cs.forM ctrace
