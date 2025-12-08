import Lean

open Lean Elab Command

def describeOpenDecls (ds : List OpenDecl) : CommandElabM (Option MessageData) := do
  let mut lines : Array MessageData := #[]
  let mut simple : Array Name := #[]
  let flush (lines : Array MessageData) (simple : Array Name) : CommandElabM (Array MessageData × Array Name) := do
    if simple.isEmpty then
      return (lines, simple)
    else
      return (lines.push <| ← `(command| open $(simple.map mkIdent)*), #[])
  for d in ds do
    match d with
    | .explicit id decl =>
      (lines, simple) ← flush lines simple
      let ns := decl.getPrefix
      let «from» := Name.mkSimple decl.getString!
      lines := lines.push <| ← `(command| open $(mkIdent ns) renaming $(mkIdent «from») → $(mkIdent id))
    | .simple ns ex =>
      if ex == [] then
        simple := simple.push ns
      else
        (lines, simple) ← flush lines simple
        lines := lines.push <| ← `(command| open $(mkIdent ns) hiding $[$(ex.toArray.map mkIdent)]*)
  (lines, _) ← flush lines simple
  return if lines.isEmpty then none else MessageData.joinSep lines.toList "\n"

elab "#print_namespace " : command => do
  logInfo <| ← `(command| namespace $(mkIdent (← getScope).currNamespace))

elab "#print_variables" : command => do
  logInfo <| ← `(command| variable $((← getScope).varDecls.map <|
    fun (s : TSyntax _) ↦ ⟨s.raw.unsetTrailing⟩)*)

elab "#print_open" : command => do
  if let some openMsg ← describeOpenDecls (← getScope).openDecls.reverse then
    logInfo <| openMsg

elab "#print_scope" : command => do
  let scope ← getScope
  let ns ← `(command| namespace $(mkIdent scope.currNamespace))
  let vars ← `(command| variable $(scope.varDecls.map <|
    fun (s : TSyntax _) ↦ ⟨s.raw.unsetTrailing⟩)*)
  logInfo <| MessageData.joinSep [ns, vars] "\n"

elab "#print_ns_section" : command => do
  let headers := ((← getScopes).map (·.header)).reverse
  let ns := (← getScope).currNamespace.toString.replace "[anonymous]" ""
  logInfo <| s!"namespace {ns}\n".append
    <| "scope ".append <| (headers.headD "").append <| ".".intercalate headers.tail

elab "#print_section" : command => do
  let headers := ((← getScopes).map (·.header)).reverse
  logInfo <| ("scope ".append <| (headers.headD "").append <| ".".intercalate headers.tail).append "\n\n"

def getUsedDecl (n : String) : MetaM (List Name) := do
  return (← getConstInfo n.toName).getUsedConstantsAsSet.toList

elab "#used_decls " n:ident : command => do
  liftTermElabM do
    let decls ← getUsedDecl n.getId.toString
    logInfo <| Format.joinSep decls "\n"
