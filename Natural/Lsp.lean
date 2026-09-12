-- Some code in this file is derived from Verso/Doc/Lsp.lean in Verso:
--   https://github.com/leanprover/verso

import Lean
import Natural.Grammar
import Natural.Util

open Lean
open Lean.Lsp
open Lean.Server
open Lean.Server.FileWorker
open Lean.Server.RequestM

namespace Natural

meta def mergeResponses (docTask : RequestTask α) (leanTask : RequestTask β)
      (f : Option α → Option β → γ) : RequestM (RequestTask γ) := do
  pure <| docTask.bindCostly fun
  | .ok docResult =>
    leanTask.bindCostly fun
    | .ok leanResult =>
      .mk <| .pure <| pure <| f (some docResult) (some leanResult)
    | .error _ => .mk <| .pure <| pure <| f (some docResult) none
  | .error _ =>
    leanTask.bindCostly fun
    | .ok leanResult => .mk <| .pure <| pure <| f none (some leanResult)
    | .error e => .pure <| throw e

structure SemanticTokenEntry where
  line : Nat
  startChar : Nat
  length : Nat
  type : Nat
  modifierMask : Nat
deriving Inhabited, Repr

instance: ToString SemanticTokenEntry where
  toString e :=
    let type := SemanticTokenType.names[e.type]!
    s!"[line = {e.line}, start = {e.startChar}, length = {e.length}, type = {type}]"

protected meta def SemanticTokenEntry.ordLe (a b : SemanticTokenEntry) : Bool :=
  a.line < b.line ∨ (a.line = b.line ∧ a.startChar <= b.startChar)

protected meta def SemanticTokenEntry.posEq (a b : SemanticTokenEntry) : Bool :=
  (a.line, a.startChar) == (b.line, b.startChar)

meta def encodeTokenEntries (entries : Array SemanticTokenEntry) : Array Nat := Id.run do
  let mut data := #[]
  let mut lastLine := 0
  let mut lastChar := 0
  for ⟨line, char, len, type, modMask⟩ in entries do
    let deltaLine := line - lastLine
    let deltaStart := if line = lastLine then char - lastChar else char
    data := data ++ #[deltaLine, deltaStart, len, type, modMask]
    lastLine := line; lastChar := char
  return data

meta def decodeLeanTokens (data : Array Nat) : Array SemanticTokenEntry := Id.run do
  let mut line := 0
  let mut char := 0
  let mut entries : Array SemanticTokenEntry := #[]
  for i in [0:data.size:5] do
    let #[deltaLine, deltaStart, len, type, modMask] := data[i:i+5].toArray
      | return entries -- If this happens, something is wrong with Lean, but we don't really care
    line := line + deltaLine
    char := if deltaLine = 0 then char + deltaStart else deltaStart
    entries := entries.push ⟨line, char, len, type, modMask⟩
  return entries

meta partial def naturalTokens (text : FileMap) (stx : Syntax) : Array SemanticTokenEntry :=
  match stx with
    | `(definition_stmt| Definition . $_d)
    | `(_theorem| $_:_thm $_name:thm_name ? $_:str ? . $[$ls:let_step .]? $_ps:props_proofs) =>
          gather stx
    | _ => stx.getArgs.flatMap (naturalTokens text)
where
  mkTok (tokenType : SemanticTokenType) (stx : Syntax) : Array SemanticTokenEntry := Id.run do
    let (some startPos, some endPos) := (stx.getPos?, stx.getTailPos?)
      | return #[]
    let startLspPos := text.utf8PosToLspPos startPos
    let endLspPos := text.utf8PosToLspPos endPos
    -- VS Code has a limitation where tokens can't span lines. The
    -- parser obeys an invariant that no token spans a line, so we can
    -- bail, rather than resorting to workarounds.
    if startLspPos.line == endLspPos.line then #[{
        line := startLspPos.line,
        startChar := startLspPos.character,
        length := endLspPos.character - startLspPos.character,
        type := tokenType.toNat,
        modifierMask := 0
      }]
    else #[]

  keywords := ["Definition", "Lemma", "Proof", "Theorem"]

  gather (stx: Syntax) := match stx with
  | `(thm_name| $i:ident)
  | `(label| $i:ident) => mkTok .function i
  | _ => match stx with
    | .ident .. => mkTok .operator stx
    | .atom _ val => mkTok (if keywords.elem val then .keyword else .operator) stx
    | _ => stx.getArgs.flatMap gather

meta def mergeTokens (mine : Array SemanticTokenEntry) (leans : SemanticTokens) : Array Nat :=
  let toks := decodeLeanTokens leans.data
  let sorted := mine ++ toks |>.mergeSort (·.ordLe ·)   -- need a stable sort here
  let merged := sorted.eraseRepsBy SemanticTokenEntry.posEq
  encodeTokenEntries merged

meta def snapshotTokens (beginPos : String.Pos.Raw) (text : FileMap)
      (snap : Snapshots.Snapshot) : Array SemanticTokenEntry :=
  if snap.endPos <= beginPos then #[] else naturalTokens text snap.stx

meta def snapshotsTokens (beginPos : String.Pos.Raw) (text : FileMap)
      (snaps : List Snapshots.Snapshot) : Array SemanticTokenEntry :=
  snaps.foldl (init := #[]) fun toks snap => toks ++ snapshotTokens beginPos text snap

meta partial def handleTokens (prev : RequestTask SemanticTokens)
    (beginPos : String.Pos.Raw) (endPos? : Option String.Pos.Raw) :
    RequestM (RequestTask (LspResponse SemanticTokens)) := do
  let ctx ← read
  let doc ← readDoc
  let text := doc.meta.text
  if let some endPos := endPos? then
    let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
    let toks : RequestTask (Array SemanticTokenEntry) :=
      t.mapCostly fun (snaps, _) => pure <| snapshotsTokens beginPos text snaps
    let response ← mergeIntoPrev toks
    return response.mapCheap fun t =>
      t.map ({ response := ·, isComplete := true })
  else
    let (snaps, _, isComplete) ←
      doc.cmdSnaps.getFinishedPrefixWithTimeout 2000 (cancelTks := ctx.cancelTk.cancellationTasks)
    let toks : Array SemanticTokenEntry := snapshotsTokens beginPos text snaps
    let response ← mergeIntoPrev (.pure toks)
    pure <| response.mapCheap fun t => t.map ({ response := ·, isComplete := isComplete })

where
  mergeIntoPrev (toks : RequestTask (Array SemanticTokenEntry)) :=
    mergeResponses toks prev fun
      | none, none => SemanticTokens.mk none #[]
      | some xs, none => SemanticTokens.mk none <| encodeTokenEntries <| xs.mergeSort (·.ordLe ·)
      | none, some r => r
      | some mine, some leans => {leans with data := mergeTokens mine leans}

meta def handleTokensRange (params : SemanticTokensRangeParams) (prev : RequestTask SemanticTokens)
      : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  handleTokens prev beginPos endPos <&> fun t => t.mapCheap (LspResponse.response <$> ·)

meta def handleTokensFullStateful
    (_params : SemanticTokensParams) (prev : LspResponse SemanticTokens)
    (st : SemanticTokensState) : RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let doc ← readDoc
  let text := doc.meta.text
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 2000
  RequestM.checkCancelled
  let toks : Array SemanticTokenEntry := snapshotsTokens 0 text snaps
  RequestM.checkCancelled
  let response := {prev with data := mergeTokens toks prev.response}
  RequestM.checkCancelled
  return ({response, isComplete}, st)

meta initialize
  chainLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams
    SemanticTokens handleTokensRange

  chainStatefulLspRequestHandler "textDocument/semanticTokens/full" SemanticTokensParams
    SemanticTokens SemanticTokensState handleTokensFullStateful handleSemanticTokensDidChange
