import ExplicitLean
-- Option declarations are process-global. Preloading all of Mathlib here
-- would activate weak linter options that an early module's own imports do
-- not register, changing its selector state relative to a standalone build.
import Lean.Elab.Frontend
import Lean.Compiler.LCNF.PhaseExt
import Lean.DocString.Extension
import Lean.Util.CollectAxioms
import Lean.ExtraModUses
import ExplicitLean.SimpEngine.CommandAudit

open Lean

namespace ExplicitLean.SimpEngine.DeclarationOracle

private def oracleToolingModule : Name :=
  `ExplicitLean.SimpEngine.Boundary.Tactic

private def oracleFailure (category detail : String) : IO α :=
  throw <| IO.userError s!"DECLARATION_ORACLE_FAILURE|{category}|{detail}"

private structure LCNFFVarMap where
  pairs : Array (FVarId × FVarId) := #[]

private def findLCNFPairsByApplied? (mapping : LCNFFVarMap)
    (fvarId : FVarId) : Option FVarId :=
  mapping.pairs.find? (fun pair => pair.1 == fvarId) |>.map (·.2)

private def findLCNFPairsByStock? (mapping : LCNFFVarMap)
    (fvarId : FVarId) : Option FVarId :=
  mapping.pairs.find? (fun pair => pair.2 == fvarId) |>.map (·.1)

private def pairLCNFFVar (mapping : LCNFFVarMap)
    (applied stock : FVarId) : Option LCNFFVarMap :=
  match findLCNFPairsByApplied? mapping applied, findLCNFPairsByStock? mapping stock with
  | some mapped, _ => if mapped == stock then some mapping else none
  | none, some _ => none
  | none, none => some { mapping with pairs := mapping.pairs.push (applied, stock) }

private partial def lcnfLevelResolved : Level → Bool
  | .zero => true
  | .param _ => true
  | .mvar _ => false
  | .succ level => lcnfLevelResolved level
  | .max lhs rhs | .imax lhs rhs => lcnfLevelResolved lhs && lcnfLevelResolved rhs

private partial def mapLCNFExpr (mapping : LCNFFVarMap) : Expr → Option Expr
  | .lit value => some (.lit value)
  | .mvar _ => none
  | .fvar id => findLCNFPairsByApplied? mapping id |>.map Expr.fvar
  | .bvar index => some (.bvar index)
  | .sort level => if lcnfLevelResolved level then some (.sort level) else none
  | .const name levels =>
      if levels.all lcnfLevelResolved then some (.const name levels) else none
  | .app fn argument => do
      return .app (← mapLCNFExpr mapping fn) (← mapLCNFExpr mapping argument)
  | .lam binderName type body binderInfo => do
      return .lam binderName (← mapLCNFExpr mapping type)
        (← mapLCNFExpr mapping body) binderInfo
  | .forallE binderName type body binderInfo => do
      return .forallE binderName (← mapLCNFExpr mapping type)
        (← mapLCNFExpr mapping body) binderInfo
  | .letE binderName type value body nondep => do
      return .letE binderName (← mapLCNFExpr mapping type)
        (← mapLCNFExpr mapping value) (← mapLCNFExpr mapping body) nondep
  | .proj typeName index body => do
      return .proj typeName index (← mapLCNFExpr mapping body)
  | .mdata data body => do
      return .mdata data (← mapLCNFExpr mapping body)

private def compareLCNFExpr (mapping : LCNFFVarMap)
    (stock applied : Expr) : Bool :=
  match mapLCNFExpr mapping applied with
  | some applied => stock == applied
  | none => false

private def compareLCNFFVar (mapping : LCNFFVarMap)
    (stock applied : FVarId) : Bool :=
  findLCNFPairsByApplied? mapping applied |>.map (· == stock) |>.getD false

private def compareLCNFLevel (stock applied : Level) : Bool :=
  lcnfLevelResolved stock && lcnfLevelResolved applied && stock == applied

private def compareLCNFLevels (stock applied : List Level) : Bool :=
  stock.length == applied.length && (stock.zip applied).all fun (stock, applied) =>
    compareLCNFLevel stock applied

private def compareLCNFArg (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.Arg .pure) : Bool :=
  match stock, applied with
  | .erased, .erased => true
  | .fvar stock, .fvar applied => compareLCNFFVar mapping stock applied
  | .type stock _, .type applied _ => compareLCNFExpr mapping stock applied
  | _, _ => false

private def compareLCNFArgs (mapping : LCNFFVarMap)
    (stock applied : Array (Compiler.LCNF.Arg .pure)) : Bool :=
  stock.size == applied.size && (stock.zip applied).all fun (stock, applied) =>
    compareLCNFArg mapping stock applied

private def compareLCNFParamFields (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.Param .pure) : Bool :=
  compareLCNFFVar mapping stock.fvarId applied.fvarId &&
    stock.binderName == applied.binderName && stock.borrow == applied.borrow &&
    compareLCNFExpr mapping stock.type applied.type

private def compareLCNFParamFieldsArray (mapping : LCNFFVarMap)
    (stock applied : Array (Compiler.LCNF.Param .pure)) : Bool :=
  stock.size == applied.size && (stock.zip applied).all fun (stock, applied) =>
    compareLCNFParamFields mapping stock applied

private def pairLCNFParams (mapping : LCNFFVarMap)
    (stock applied : Array (Compiler.LCNF.Param .pure)) : Option LCNFFVarMap := do
  unless stock.size == applied.size do guard false
  let mut mapping := mapping
  for (stock, applied) in stock.zip applied do
    mapping ← pairLCNFFVar mapping applied.fvarId stock.fvarId
  return mapping

private def compareLCNFCtorInfo
    (stock applied : Compiler.LCNF.CtorInfo) : Bool :=
  stock == applied

private def compareLCNFLetValue (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.LetValue .pure) : Bool :=
  match stock, applied with
  | .lit stock, .lit applied => stock == applied
  | .erased, .erased => true
  | .proj stockName stockIndex stockStruct _, .proj appliedName appliedIndex appliedStruct _ =>
      stockName == appliedName && stockIndex == appliedIndex &&
        compareLCNFFVar mapping stockStruct appliedStruct
  | .const stockName stockLevels stockArgs _, .const appliedName appliedLevels appliedArgs _ =>
      stockName == appliedName && compareLCNFLevels stockLevels appliedLevels &&
        compareLCNFArgs mapping stockArgs appliedArgs
  | .fvar stockFVar stockArgs, .fvar appliedFVar appliedArgs =>
      compareLCNFFVar mapping stockFVar appliedFVar &&
        compareLCNFArgs mapping stockArgs appliedArgs
  | .ctor stockInfo stockArgs _, .ctor appliedInfo appliedArgs _ =>
      compareLCNFCtorInfo stockInfo appliedInfo && compareLCNFArgs mapping stockArgs appliedArgs
  | .oproj stockIndex stockVar _, .oproj appliedIndex appliedVar _ =>
      stockIndex == appliedIndex && compareLCNFFVar mapping stockVar appliedVar
  | .uproj stockIndex stockVar _, .uproj appliedIndex appliedVar _ =>
      stockIndex == appliedIndex && compareLCNFFVar mapping stockVar appliedVar
  | .sproj stockIndex stockOffset stockVar _, .sproj appliedIndex appliedOffset appliedVar _ =>
      stockIndex == appliedIndex && stockOffset == appliedOffset &&
        compareLCNFFVar mapping stockVar appliedVar
  | .fap stockName stockArgs _, .fap appliedName appliedArgs _ =>
      stockName == appliedName && compareLCNFArgs mapping stockArgs appliedArgs
  | .pap stockName stockArgs _, .pap appliedName appliedArgs _ =>
      stockName == appliedName && compareLCNFArgs mapping stockArgs appliedArgs
  | .reset stockCount stockVar _, .reset appliedCount appliedVar _ =>
      stockCount == appliedCount && compareLCNFFVar mapping stockVar appliedVar
  | .reuse stockVar stockInfo stockHeader stockArgs _,
      .reuse appliedVar appliedInfo appliedHeader appliedArgs _ =>
      compareLCNFFVar mapping stockVar appliedVar &&
        compareLCNFCtorInfo stockInfo appliedInfo && stockHeader == appliedHeader &&
        compareLCNFArgs mapping stockArgs appliedArgs
  | .box stockType stockVar _, .box appliedType appliedVar _ =>
      compareLCNFExpr mapping stockType appliedType &&
        compareLCNFFVar mapping stockVar appliedVar
  | .unbox stockVar _, .unbox appliedVar _ => compareLCNFFVar mapping stockVar appliedVar
  | .isShared stockVar _, .isShared appliedVar _ => compareLCNFFVar mapping stockVar appliedVar
  | _, _ => false

private def compareLCNFParams (mapping : LCNFFVarMap)
    (stock applied : Array (Compiler.LCNF.Param .pure)) : Option LCNFFVarMap := do
  let mapping ← pairLCNFParams mapping stock applied
  unless compareLCNFParamFieldsArray mapping stock applied do
    guard false
  return mapping

mutual

private partial def compareLCNFLetDecl (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.LetDecl .pure) : Option LCNFFVarMap := do
  let mapping ← pairLCNFFVar mapping applied.fvarId stock.fvarId
  unless stock.binderName == applied.binderName &&
      compareLCNFExpr mapping stock.type applied.type &&
      compareLCNFLetValue mapping stock.value applied.value do
    guard false
  return mapping

private partial def compareLCNFFunDecl (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.FunDecl .pure) : Option LCNFFVarMap := do
  let mapping ← pairLCNFFVar mapping applied.fvarId stock.fvarId
  let mapping ← compareLCNFParams mapping stock.params applied.params
  unless stock.binderName == applied.binderName &&
      compareLCNFExpr mapping stock.type applied.type do
    guard false
  compareLCNFCode mapping stock.value applied.value

private partial def compareLCNFAlt (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.Alt .pure) : Option LCNFFVarMap := do
  match stock, applied with
  | .alt stockCtor stockParams stockCode, .alt appliedCtor appliedParams appliedCode =>
      unless stockCtor == appliedCtor do guard false
      let mapping ← compareLCNFParams mapping stockParams appliedParams
      compareLCNFCode mapping stockCode appliedCode
  | .ctorAlt stockInfo stockCode _, .ctorAlt appliedInfo appliedCode _ =>
      unless compareLCNFCtorInfo stockInfo appliedInfo do guard false
      compareLCNFCode mapping stockCode appliedCode
  | .default stockCode, .default appliedCode =>
      compareLCNFCode mapping stockCode appliedCode
  | _, _ => none

private partial def compareLCNFAlts (mapping : LCNFFVarMap)
    (stock applied : Array (Compiler.LCNF.Alt .pure)) : Option LCNFFVarMap := do
  unless stock.size == applied.size do guard false
  let mut mapping := mapping
  for (stock, applied) in stock.zip applied do
    mapping ← compareLCNFAlt mapping stock applied
  return mapping

private partial def compareLCNFCases (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.Cases .pure) : Option LCNFFVarMap := do
  unless stock.typeName == applied.typeName &&
      compareLCNFFVar mapping stock.discr applied.discr &&
      compareLCNFExpr mapping stock.resultType applied.resultType do
    guard false
  compareLCNFAlts mapping stock.alts applied.alts

private partial def compareLCNFCode (mapping : LCNFFVarMap)
    (stock applied : Compiler.LCNF.Code .pure) : Option LCNFFVarMap := do
  match stock, applied with
  | .let stockDecl stockK, .let appliedDecl appliedK =>
      let mapping ← compareLCNFLetDecl mapping stockDecl appliedDecl
      compareLCNFCode mapping stockK appliedK
  | .fun stockDecl stockK _, .fun appliedDecl appliedK _ =>
      let mapping ← compareLCNFFunDecl mapping stockDecl appliedDecl
      compareLCNFCode mapping stockK appliedK
  | .jp stockDecl stockK, .jp appliedDecl appliedK =>
      let mapping ← compareLCNFFunDecl mapping stockDecl appliedDecl
      compareLCNFCode mapping stockK appliedK
  | .jmp stockFVar stockArgs, .jmp appliedFVar appliedArgs =>
      unless compareLCNFFVar mapping stockFVar appliedFVar &&
          compareLCNFArgs mapping stockArgs appliedArgs do
        guard false
      return mapping
  | .cases stockCases, .cases appliedCases =>
      compareLCNFCases mapping stockCases appliedCases
  | .return stockFVar, .return appliedFVar =>
      unless compareLCNFFVar mapping stockFVar appliedFVar do guard false
      return mapping
  | .unreach stockType, .unreach appliedType =>
      unless compareLCNFExpr mapping stockType appliedType do guard false
      return mapping
  | .oset stockFVar stockIndex stockArg stockK _,
      .oset appliedFVar appliedIndex appliedArg appliedK _ =>
      unless stockIndex == appliedIndex && compareLCNFFVar mapping stockFVar appliedFVar &&
          compareLCNFArg mapping stockArg appliedArg do
        guard false
      compareLCNFCode mapping stockK appliedK
  | .uset stockFVar stockIndex stockValue stockK _,
      .uset appliedFVar appliedIndex appliedValue appliedK _ =>
      unless stockIndex == appliedIndex && compareLCNFFVar mapping stockFVar appliedFVar &&
          compareLCNFFVar mapping stockValue appliedValue do
        guard false
      compareLCNFCode mapping stockK appliedK
  | .sset stockFVar stockIndex stockOffset stockValue stockType stockK _,
      .sset appliedFVar appliedIndex appliedOffset appliedValue appliedType appliedK _ =>
      unless stockIndex == appliedIndex && stockOffset == appliedOffset &&
          compareLCNFFVar mapping stockFVar appliedFVar &&
          compareLCNFFVar mapping stockValue appliedValue &&
          compareLCNFExpr mapping stockType appliedType do
        guard false
      compareLCNFCode mapping stockK appliedK
  | .setTag stockFVar stockIndex stockK _, .setTag appliedFVar appliedIndex appliedK _ =>
      unless stockIndex == appliedIndex && compareLCNFFVar mapping stockFVar appliedFVar do
        guard false
      compareLCNFCode mapping stockK appliedK
  | .inc stockFVar stockCount stockCheck stockPersistent stockK _,
      .inc appliedFVar appliedCount appliedCheck appliedPersistent appliedK _ =>
      unless stockCount == appliedCount && stockCheck == appliedCheck &&
          stockPersistent == appliedPersistent && compareLCNFFVar mapping stockFVar appliedFVar do
        guard false
      compareLCNFCode mapping stockK appliedK
  | .dec stockFVar stockCount stockCheck stockPersistent stockObjects stockK _,
      .dec appliedFVar appliedCount appliedCheck appliedPersistent appliedObjects appliedK _ =>
      unless stockCount == appliedCount && stockCheck == appliedCheck &&
          stockPersistent == appliedPersistent && stockObjects == appliedObjects &&
          compareLCNFFVar mapping stockFVar appliedFVar do
        guard false
      compareLCNFCode mapping stockK appliedK
  | .del stockFVar stockK _, .del appliedFVar appliedK _ =>
      unless compareLCNFFVar mapping stockFVar appliedFVar do guard false
      compareLCNFCode mapping stockK appliedK
  | _, _ => none

end

private def compareLCNFDecl
    (stock applied : Compiler.LCNF.Decl .pure) : Bool :=
  if stock.name != applied.name || stock.levelParams != applied.levelParams ||
      stock.safe != applied.safe || stock.recursive != applied.recursive ||
      stock.inlineAttr? != applied.inlineAttr? then
    false
  else
    match compareLCNFParams {} stock.params applied.params with
    | none => false
    | some mapping =>
        compareLCNFExpr mapping stock.type applied.type &&
        match stock.value, applied.value with
        | .code stockCode, .code appliedCode =>
            (compareLCNFCode mapping stockCode appliedCode).isSome
        | .extern stockExtern, .extern appliedExtern => stockExtern == appliedExtern
        | _, _ => false

private unsafe def sortedLCNFDecls
    (state : Compiler.LCNF.DeclExtState .pure) : Array (Name × Compiler.LCNF.Decl .pure) :=
  state.toArray.qsort (fun lhs rhs => lhs.1.toString < rhs.1.toString)

private unsafe def compareLCNFDeclState (label : String)
    (stock applied : Compiler.LCNF.DeclExtState .pure) : IO Unit := do
  let stockEntries := sortedLCNFDecls stock
  let appliedEntries := sortedLCNFDecls applied
  unless stockEntries.map (·.1) == appliedEntries.map (·.1) do
    oracleFailure "environment_delta_mismatch" s!"typed {label} declaration name set differs"
  for (stockEntry, appliedEntry) in stockEntries.zip appliedEntries do
    unless compareLCNFDecl stockEntry.2 appliedEntry.2 do
      oracleFailure "environment_delta_mismatch"
        s!"typed {label} declaration differs for {stockEntry.1}"

private unsafe def compareLCNFExtensions (stock applied : Environment) : IO Unit := do
  compareLCNFDeclState "baseExt" (Compiler.LCNF.baseExt.getState stock)
    (Compiler.LCNF.baseExt.getState applied)
  compareLCNFDeclState "monoExt" (Compiler.LCNF.monoExt.getState stock)
    (Compiler.LCNF.monoExt.getState applied)

private def isModuleDocExtensionName (name : Name) : Bool :=
  name.toString == "_private.Lean.DocString.Extension.0.Lean.moduleDocExt"

private def isExtraModUsesExtensionName (name : Name) : Bool :=
  name.toString == "_private.Lean.ExtraModUses.0.Lean.extraModUses"

private def isExportedAxiomsExtensionName (name : Name) : Bool :=
  name.toString ==
    "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt"

private def isPrivateConstKindsExtensionName (name : Name) : Bool :=
  name.toString ==
    "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt"

private def runExtensionNameSelfTest : IO Unit := do
  if isModuleDocExtensionName `Project.moduleDocExt ||
      isExtraModUsesExtensionName `Project.extraModUses ||
      isExportedAxiomsExtensionName `Project.exportedAxiomsExt ||
      isPrivateConstKindsExtensionName `Project.privateConstKindsExt then
    throw <| IO.userError "extension-name self-test accepted a suffix lookalike"

private def runLCNFComparatorSelfTest : IO Unit := do
  let stockParamId : FVarId := ⟨`lcnfStockParam⟩
  let stockLetId : FVarId := ⟨`lcnfStockLet⟩
  let appliedParamId : FVarId := ⟨`lcnfAppliedParam⟩
  let appliedLetId : FVarId := ⟨`lcnfAppliedLet⟩
  let stockParam : Compiler.LCNF.Param .pure := {
    fvarId := stockParamId
    binderName := `param
    type := .const ``Nat []
    borrow := false
  }
  let appliedParam : Compiler.LCNF.Param .pure := {
    fvarId := appliedParamId
    binderName := `param
    type := .const ``Nat []
    borrow := false
  }
  let stockLet : Compiler.LCNF.LetDecl .pure := {
    fvarId := stockLetId
    binderName := `value
    type := .const ``Nat []
    value := .lit (.nat 1)
  }
  let appliedLet : Compiler.LCNF.LetDecl .pure := {
    fvarId := appliedLetId
    binderName := `value
    type := .const ``Nat []
    value := .lit (.nat 1)
  }
  let stock : Compiler.LCNF.Decl .pure := {
    name := `lcnfComparatorSelfTest
    levelParams := []
    type := .const ``Nat []
    params := #[stockParam]
    safe := true
    value := .code (.let stockLet (.return stockLetId))
    recursive := false
    inlineAttr? := none
  }
  let applied : Compiler.LCNF.Decl .pure := {
    name := `lcnfComparatorSelfTest
    levelParams := []
    type := .const ``Nat []
    params := #[appliedParam]
    safe := true
    value := .code (.let appliedLet (.return appliedLetId))
    recursive := false
    inlineAttr? := none
  }
  unless compareLCNFDecl stock applied do
    throw <| IO.userError "LCNF comparator self-test rejected alpha-renamed let"
  let changedLet : Compiler.LCNF.Decl .pure :=
    { applied with
      value := .code (.let { appliedLet with value := .lit (.nat 2) }
        (.return appliedLetId)) }
  if compareLCNFDecl stock changedLet then
    throw <| IO.userError "LCNF comparator self-test accepted changed let value"
  let changedReturn : Compiler.LCNF.Decl .pure :=
    { applied with value := .code (.return appliedParamId) }
  if compareLCNFDecl stock changedReturn then
    throw <| IO.userError "LCNF comparator self-test accepted changed return"
  let unresolvedUniverse : Compiler.LCNF.Decl .pure :=
    { applied with type := .sort (.mvar ⟨`lcnfUniverseMVar⟩) }
  if compareLCNFDecl stock unresolvedUniverse then
    throw <| IO.userError "LCNF comparator self-test accepted universe metavariable"

private def allowlistedExtension (name : Name) : Bool :=
  name == `Lean.declRangeExt ||
  isExportedAxiomsExtensionName name ||
  isPrivateConstKindsExtensionName name ||
  isExtraModUsesExtensionName name

private def constantKind : ConstantInfo → String
  | .axiomInfo .. => "axiom"
  | .defnInfo .. => "definition"
  | .thmInfo .. => "theorem"
  | .opaqueInfo .. => "opaque"
  | .quotInfo .. => "quotient"
  | .inductInfo .. => "inductive"
  | .ctorInfo .. => "constructor"
  | .recInfo .. => "recursor"

private structure OracleCounts where
  stockDeclarations : Nat := 0
  appliedDeclarations : Nat := 0
  commonPublicDeclarations : Nat := 0
  stockOnlyPrivateProof : Nat := 0
  appliedOnlyPrivateProof : Nat := 0
  stockExtensions : Nat := 0
  appliedExtensions : Nat := 0
  checkedDeclarations : Nat := 0

private structure OracleResult where
  counts : OracleCounts

private unsafe def elaborateSource (moduleName : Name) (auditLabel : String)
    (path : System.FilePath) (oleanFileName? : Option System.FilePath := none) : IO Environment := do
  Lean.enableInitializersExecution
  let source ← IO.FS.readFile path
  -- Keep this in sync with `simp_engine_inventory.py`; async elaboration is
  -- deliberately enabled because it affects declaration selection.
  let options := Elab.async.set (Elab.autoImplicit.set {} false) true
    |>.set `maxSynthPendingDepth (3 : Nat)
    |>.set `weak.linter.unusedVariables false
    |>.set `weak.linter.unusedSimpArgs false
    |>.set `weak.linter.unreachableTactic false
    |>.set `maxHeartbeats (0 : Nat)
  if (← IO.getEnv CommandAudit.enabledVariable) == some "1" then
    let nonce ← CommandAudit.runNonce
    let captured ← try
      CommandAudit.capture source options path.toString moduleName (oleanFileName? := oleanFileName?)
    catch error =>
      if error.toString == "command_audit_frontend_failed" then
        oracleFailure "unresolved_or_sorry" s!"frontend returned no environment for {path}"
      else
        throw error
    CommandAudit.emit captured auditLabel nonce
    return captured.environment
  let some environment ← Elab.runFrontend source options path.toString moduleName (oleanFileName? := oleanFileName?)
    | oracleFailure "unresolved_or_sorry" s!"frontend returned no environment for {path}"
  return environment

-- Keep the frontend's retained-import invariant without replaying any state.
private def validateFrontendEnvironment (environment : Environment) : IO Unit := do
  unless environment.importEnv?.isSome do
    oracleFailure "unresolved_or_sorry" "frontend did not retain its import environment"

private def sortedCurrentDeclarations (environment : Environment) : IO (Array ConstantInfo) := do
  let data ← Lean.mkModuleData environment
  return data.constants.filter (fun info => !environment.isImportedConst info.name)
    |>.qsort (fun lhs rhs => lhs.name.toString < rhs.name.toString)

private def declarationMap (declarations : Array ConstantInfo) : NameMap ConstantInfo :=
  declarations.foldl (init := {}) fun map info => map.insert info.name info

private def uniqueNames (names : Array Name) : Array Name := Id.run do
  let mut result : Array Name := #[]
  for name in names do
    unless result.contains name do
      result := result.push name
  return result

private def boundedNameList (names : Array Name) : String :=
  let limit := 32
  let shown := names.extract 0 (min limit names.size)
  let rendered := String.intercalate "," (shown.toList.map Name.toString)
  if names.size > limit then s!"[{rendered},...](truncated)" else s!"[{rendered}]"

private def declarationNameSetMismatchDetail
    (stockPublicNames appliedPublicNames : Array Name) : String :=
  let stockOnly := stockPublicNames.filter (fun name => !appliedPublicNames.contains name)
  let appliedOnly := appliedPublicNames.filter (fun name => !stockPublicNames.contains name)
  s!"non-private declaration name set differs; stockCount={stockPublicNames.size}; " ++
    s!"appliedCount={appliedPublicNames.size}; stockOnlyCount={stockOnly.size}; " ++
    s!"appliedOnlyCount={appliedOnly.size}; stockOnly={boundedNameList stockOnly}; " ++
    s!"appliedOnly={boundedNameList appliedOnly}"

-- A generated-looking suffix does not establish private provenance: users can
-- legally export names such as `proof_1`. Keep every such public declaration.
private def privateDeclarationName (name : Name) : Bool :=
  isPrivateName name

private unsafe def runMetaInEnvironment (environment : Environment) (action : MetaM α) : IO α :=
  PPContext.runMetaM { env := environment } action

private unsafe def isPropInEnvironment (environment : Environment) (type : Expr) : IO Bool :=
  runMetaInEnvironment environment (Meta.isProp type)

private unsafe def isDefEqInEnvironment (environment : Environment)
    (lhs rhs : Expr) : IO Bool :=
  runMetaInEnvironment environment (Meta.isDefEq lhs rhs)

private def checkExpressionResolved (label : String) (expression : Expr) : IO Unit := do
  if expression.hasExprMVar || expression.hasLevelMVar || expression.hasFVar then
    oracleFailure "unresolved_or_sorry" s!"unresolved expression in {label}"
  if expression.hasSorry then
    oracleFailure "unresolved_or_sorry" s!"sorryAx in {label}"

private def metadataEqual (stock applied : ConstantInfo) : Bool :=
  match stock, applied with
  | .axiomInfo stock, .axiomInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.isUnsafe == applied.isUnsafe
  | .defnInfo stock, .defnInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.hints == applied.hints && stock.safety == applied.safety &&
        stock.all == applied.all
  | .thmInfo stock, .thmInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.all == applied.all
  | .opaqueInfo stock, .opaqueInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.isUnsafe == applied.isUnsafe && stock.all == applied.all
  | .quotInfo stock, .quotInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        match stock.kind, applied.kind with
        | .type, .type => true
        | .ctor, .ctor => true
        | .lift, .lift => true
        | .ind, .ind => true
        | _, _ => false
  | .inductInfo stock, .inductInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.numParams == applied.numParams && stock.numIndices == applied.numIndices &&
        stock.all == applied.all && stock.ctors == applied.ctors &&
        stock.numNested == applied.numNested && stock.isRec == applied.isRec &&
        stock.isUnsafe == applied.isUnsafe && stock.isReflexive == applied.isReflexive
  | .ctorInfo stock, .ctorInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.induct == applied.induct && stock.cidx == applied.cidx &&
        stock.numParams == applied.numParams && stock.numFields == applied.numFields &&
        stock.isUnsafe == applied.isUnsafe
  | .recInfo stock, .recInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.all == applied.all && stock.numParams == applied.numParams &&
        stock.numIndices == applied.numIndices && stock.numMotives == applied.numMotives &&
        stock.numMinors == applied.numMinors && stock.k == applied.k &&
        stock.isUnsafe == applied.isUnsafe && stock.rules.length == applied.rules.length &&
        (List.zipWith (fun stockRule appliedRule =>
          stockRule.ctor == appliedRule.ctor && stockRule.nfields == appliedRule.nfields)
          stock.rules applied.rules).all (fun value => value)
  | _, _ => false

private unsafe def compareRecursorRules (stockEnvironment : Environment)
    (stock applied : ConstantInfo) (label : String) : IO Unit := do
  match stock, applied with
  | .recInfo stock, .recInfo applied =>
      for (stockRule, appliedRule) in List.zip stock.rules applied.rules do
        unless ← isDefEqInEnvironment stockEnvironment stockRule.rhs appliedRule.rhs do
          oracleFailure "declaration_metadata_mismatch" s!"recursor rule mismatch in {label}"
  | _, _ => pure ()

private unsafe def compareDeclaration (stockEnvironment appliedEnvironment : Environment)
    (stock applied : ConstantInfo) (label : String) : IO Unit := do
  unless metadataEqual stock applied do
    oracleFailure "declaration_metadata_mismatch" s!"{label} ({constantKind stock})"
  unless ← isDefEqInEnvironment stockEnvironment stock.type applied.type do
    oracleFailure "declaration_type_mismatch" label
  compareRecursorRules stockEnvironment stock applied label
  if stock.type.hasSorry || applied.type.hasSorry then
    oracleFailure "unresolved_or_sorry" s!"sorryAx in type of {label}"
  match applied.value? (allowOpaque := true) with
  | some appliedValue =>
      checkExpressionResolved s!"value of {label}" appliedValue
      if ← isPropInEnvironment appliedEnvironment applied.type then
        pure ()
      else
        match stock.value? (allowOpaque := true) with
        | some stockValue =>
            unless ← isDefEqInEnvironment stockEnvironment stockValue appliedValue do
              oracleFailure "declaration_value_mismatch" label
        | none => oracleFailure "declaration_value_mismatch" s!"missing stock value for {label}"
  | none =>
      match stock.value? (allowOpaque := true) with
      | some _ => oracleFailure "declaration_value_mismatch" s!"missing applied value for {label}"
      | none => pure ()

private unsafe def privateProofDeclaration (environment : Environment)
    (info : ConstantInfo) : IO Bool := do
  if !privateDeclarationName info.name then
    return false
  match info with
  | .thmInfo _ => pure true
  | .defnInfo _ | .opaqueInfo _ => isPropInEnvironment environment info.type
  | _ => pure false

private unsafe def checkDeclarationSets (stockEnvironment appliedEnvironment : Environment)
    (stockDeclarations appliedDeclarations : Array ConstantInfo) (counts : OracleCounts) :
    IO OracleCounts := do
  let stockMap := declarationMap stockDeclarations
  let appliedMap := declarationMap appliedDeclarations
  let stockPublic := stockDeclarations.filter
    (fun info => !privateDeclarationName info.name)
  let appliedPublic := appliedDeclarations.filter
    (fun info => !privateDeclarationName info.name)
  let stockPublicNames := stockPublic.map (·.name)
  let appliedPublicNames := appliedPublic.map (·.name)
  unless stockPublicNames == appliedPublicNames do
    oracleFailure "declaration_set_mismatch"
      (declarationNameSetMismatchDetail stockPublicNames appliedPublicNames)
  let mut result := { counts with commonPublicDeclarations := stockPublic.size }
  for stockInfo in stockDeclarations do
    if let some appliedInfo := appliedMap.find? stockInfo.name then
      let stockPrivateProof ← privateProofDeclaration stockEnvironment stockInfo
      let appliedPrivateProof ← privateProofDeclaration appliedEnvironment appliedInfo
      unless stockPrivateProof == appliedPrivateProof do
        oracleFailure "declaration_set_mismatch"
          s!"private-proof classification differs for {stockInfo.name}"
      unless stockPrivateProof do
        compareDeclaration stockEnvironment appliedEnvironment stockInfo appliedInfo
          s!"{stockInfo.name}"
      result := { result with checkedDeclarations := result.checkedDeclarations + 1 }
    else
      unless ← privateProofDeclaration stockEnvironment stockInfo do
        oracleFailure "declaration_set_mismatch" s!"stock-only non-proof declaration {stockInfo.name}"
      result := { result with stockOnlyPrivateProof := result.stockOnlyPrivateProof + 1 }
  for appliedInfo in appliedDeclarations do
    if stockMap.find? appliedInfo.name |>.isNone then
      unless ← privateProofDeclaration appliedEnvironment appliedInfo do
        oracleFailure "declaration_set_mismatch" s!"applied-only non-proof declaration {appliedInfo.name}"
      result := { result with appliedOnlyPrivateProof := result.appliedOnlyPrivateProof + 1 }
  return result

private unsafe def checkAppliedExpressions (declarations : Array ConstantInfo) : IO Unit := do
  for info in declarations do
    checkExpressionResolved s!"type of {info.name}" info.type
    match info.value? (allowOpaque := true) with
    | some value => checkExpressionResolved s!"value of {info.name}" value
    | none => pure ()
    match info with
    | .recInfo value =>
        for rule in value.rules do
          checkExpressionResolved s!"recursor rule of {info.name}" rule.rhs
    | _ => pure ()

private unsafe def collectAxiomsInEnvironment (environment : Environment) (name : Name) :
    IO (Array Name) :=
  runMetaInEnvironment environment (Lean.collectAxioms name)

private unsafe def checkAxiomSubset (stockEnvironment appliedEnvironment : Environment)
    (stockDeclarations appliedDeclarations : Array ConstantInfo) : IO Unit := do
  let stockMap := declarationMap stockDeclarations
  for appliedInfo in appliedDeclarations do
    if !privateDeclarationName appliedInfo.name then
      let some _ := stockMap.find? appliedInfo.name
        | oracleFailure "declaration_set_mismatch" s!"missing stock declaration {appliedInfo.name}"
      let stockAxioms ← collectAxiomsInEnvironment stockEnvironment appliedInfo.name
      let appliedAxioms ← collectAxiomsInEnvironment appliedEnvironment appliedInfo.name
      unless appliedAxioms.all stockAxioms.contains do
        oracleFailure "axiom_subset_mismatch" s!"axioms of {appliedInfo.name} are not a stock subset"

private def normalizedModuleData (data : ModuleData)
    (entries : Array (Name × Array EnvExtensionEntry)) : ModuleData :=
  { data with
    imports := #[]
    constNames := #[]
    constants := #[]
    extraConstNames := #[]
    entries }

private unsafe def serializeNormalizedModuleData (data : ModuleData) : IO ByteArray := do
  IO.FS.withTempFile fun _ path => do
    let compactor ← CompactedRegion.save path `_declaration_oracle data #[] none
    Runtime.forget compactor
    IO.FS.readBinFile path

private unsafe def extensionBytes (data : ModuleData)
    (name : Name) (entries : Array EnvExtensionEntry) : IO ByteArray := do
  let normalized := normalizedModuleData data #[(name, entries)]
  let first ← serializeNormalizedModuleData normalized
  let second ← serializeNormalizedModuleData normalized
  unless first == second do
    oracleFailure "environment_delta_mismatch" s!"non-deterministic serialization for extension {name}"
  return first

private unsafe def extensionMap (data : ModuleData) :
    Array (Name × Array EnvExtensionEntry) :=
  data.entries.qsort (fun lhs rhs => lhs.1.toString < rhs.1.toString)

private unsafe def currentModuleDocs (data : ModuleData) : Array ModuleDoc :=
  match data.entries.find? (fun entry => isModuleDocExtensionName entry.1) with
  | some (_, entries) => unsafeCast entries
  | none => #[]

private unsafe def compareModuleDocs (stockData appliedData : ModuleData) : IO Unit := do
  let stock := currentModuleDocs stockData
  let applied := currentModuleDocs appliedData
  unless stock.size == applied.size do
    oracleFailure "environment_delta_mismatch" "module-document count differs"
  for h : index in *...stock.size do
    let some appliedDoc := applied[index]?
      | oracleFailure "environment_delta_mismatch" "module-document count differs"
    unless stock[index].doc == appliedDoc.doc do
      oracleFailure "environment_delta_mismatch"
        s!"module-document text differs at index {index}"

/- Inlining entries belong to named declarations. Replacing a proof may rename
   private proof-valued matchers, which the declaration comparison already
   permits. Ignore only entries whose declaration satisfies that same policy;
   retain exact names and kinds for every public or computational declaration.
   ModuleData also contains checked async realization declarations that need
   not be visible on the final elaboration branch. Resolve metadata owners in
   that same checked declaration domain, without triggering realizations.
   The cast is specific to Lean.Compiler.inlineAttrs' pinned entry type. -/
private unsafe def observableInlineAttributes (environment : Environment)
    (entries : Array EnvExtensionEntry) : IO (Array (Name × Compiler.InlineAttributeKind)) := do
  let entries : Array (Name × Compiler.InlineAttributeKind) := unsafeCast entries
  let mut result := #[]
  for (name, kind) in entries do
    let some info := environment.constants.find? name
      | oracleFailure "environment_delta_mismatch" s!"inline attribute has no declaration: {name}"
    unless ← privateProofDeclaration environment info do
      result := result.push (name, kind)
  return result.qsort (fun lhs rhs => Name.quickLt lhs.1 rhs.1)

private unsafe def observableMatcherEntries (environment : Environment)
    (entries : Array EnvExtensionEntry) : IO (Array EnvExtensionEntry) := do
  let entries : Array Meta.Match.Extension.Entry := unsafeCast entries
  let mut result := #[]
  for entry in entries do
    let some info := environment.constants.find? entry.name
      | oracleFailure "environment_delta_mismatch"
          s!"matcher metadata has no declaration: {entry.name}"
    unless ← privateProofDeclaration environment info do
      result := result.push entry
  -- This is an ordered entry log: repeated names overwrite earlier metadata.
  -- Preserve order as well as every field after filtering private proofs.
  return unsafeCast result

private unsafe def compareExtensions (stockEnvironment appliedEnvironment : Environment)
    (stockData appliedData : ModuleData) : IO Unit := do
  let stockEntries := extensionMap stockData
  let appliedEntries := extensionMap appliedData
  let stockMap : NameMap (Array EnvExtensionEntry) :=
    stockEntries.foldl (init := {}) fun map entry => map.insert entry.1 entry.2
  let appliedMap : NameMap (Array EnvExtensionEntry) :=
    appliedEntries.foldl (init := {}) fun map entry => map.insert entry.1 entry.2
  let names := uniqueNames (stockEntries.map (·.1) ++ appliedEntries.map (·.1))
    |>.qsort (fun lhs rhs => lhs.toString < rhs.toString)
  for name in names do
    if name == `Lean.Compiler.LCNF.baseExt || name == `Lean.Compiler.LCNF.monoExt then
      continue
    if isModuleDocExtensionName name then
      continue
    if allowlistedExtension name then
      continue
    if name == `Lean.Compiler.inlineAttrs then
      let stock ← observableInlineAttributes stockEnvironment ((stockMap.find? name).getD #[])
      let applied ← observableInlineAttributes appliedEnvironment ((appliedMap.find? name).getD #[])
      unless stock == applied do
        oracleFailure "environment_delta_mismatch" "observable inline attributes differ"
      continue
    if name == `Lean.Meta.Match.Extension.extension then
      let stock ← observableMatcherEntries stockEnvironment ((stockMap.find? name).getD #[])
      let applied ← observableMatcherEntries appliedEnvironment ((appliedMap.find? name).getD #[])
      unless (← extensionBytes stockData name stock) == (← extensionBytes appliedData name applied) do
        oracleFailure "environment_delta_mismatch" s!"extension state differs for {name}"
      continue
    let some stockValues := stockMap.find? name
      | oracleFailure "environment_delta_mismatch" s!"stock is missing extension {name}"
    let some appliedValues := appliedMap.find? name
      | oracleFailure "environment_delta_mismatch" s!"applied is missing extension {name}"
    let stockBytes ← extensionBytes stockData name stockValues
    let appliedBytes ← extensionBytes appliedData name appliedValues
    unless stockBytes == appliedBytes do
      oracleFailure "environment_delta_mismatch" s!"extension state differs for {name}"

private def importIsTooling (imp : Import) : Bool :=
  imp.module == oracleToolingModule && !imp.importAll && !imp.isExported && !imp.isMeta

private def compareDirectImports (stock applied : Environment) : IO Unit := do
  let stockImports := stock.header.imports
  let appliedImports := applied.header.imports
  let toolingModuleImports := (stockImports ++ appliedImports).filter
    (fun imp => imp.module == oracleToolingModule)
  unless toolingModuleImports.all importIsTooling do
    oracleFailure "environment_delta_mismatch" "tooling import has unexpected flags"
  let stockToolingImports := stockImports.filter importIsTooling
  let appliedToolingImports := appliedImports.filter importIsTooling
  unless stockToolingImports.size <= 1 && appliedToolingImports.size <= 1 do
    oracleFailure "environment_delta_mismatch" "duplicate tooling import"
  let stockNonTooling := stockImports.filter (fun imp => !importIsTooling imp)
  let appliedNonTooling := appliedImports.filter (fun imp => !importIsTooling imp)
  unless stockNonTooling == appliedNonTooling do
    oracleFailure "environment_delta_mismatch" "ordered non-tooling direct imports differ"

private unsafe def currentExtraModUses (data : ModuleData) : Array ExtraModUse :=
  match data.entries.find? (fun entry => isExtraModUsesExtensionName entry.1) with
  | some (_, entries) => unsafeCast entries
  | none => #[]

private unsafe def normalizedExtraModUses (uses : Array ExtraModUse) :
    Array ExtraModUse :=
  let unique := uses.foldl (init := #[]) fun result use =>
    if result.contains use then result else result.push use
  unique.qsort (fun lhs rhs =>
    let lhsKey := s!"{lhs.module}|{lhs.isExported}|{lhs.isMeta}"
    let rhsKey := s!"{rhs.module}|{rhs.isExported}|{rhs.isMeta}"
    lhsKey < rhsKey)

private unsafe def compareExtraModUses (stockData appliedData : ModuleData) : IO Unit := do
  let stock := normalizedExtraModUses (currentExtraModUses stockData)
  let applied := normalizedExtraModUses (currentExtraModUses appliedData)
  let stockNonTooling := stock.filter (fun use => use.module != oracleToolingModule)
  let appliedNonTooling := applied.filter (fun use => use.module != oracleToolingModule)
  unless appliedNonTooling.all stockNonTooling.contains do
    oracleFailure "environment_delta_mismatch"
      "applied non-tooling extraModUses are not a stock subset"

private unsafe def compareEnvironment (stock applied : Environment)
    (stockData appliedData : ModuleData) : IO Unit := do
  compareDirectImports stock applied
  compareLCNFExtensions stock applied
  compareModuleDocs stockData appliedData
  compareExtensions stock applied stockData appliedData
  compareExtraModUses stockData appliedData

/- Bridge-v2 reads the normal compiler output; it must never re-run export
   callbacks. ModuleData has exactly six fields. isModule/imports are bound to
   the raw frontend header (ModuleHeader's two fields); constNames is derived
   from constants with duplicate rejection; constants are checked below;
   extraConstNames is exact across sources; entries use the existing typed or
   serialized extension policy. The .ir ModuleData is checked independently. -/
private structure SerializedFamily where
  parts : Array ModuleData
  regions : Array CompactedRegion
  ir? : Option (ModuleData × CompactedRegion)

private def exactConstantInfo (a b : ConstantInfo) : Bool :=
  -- Expr's default BEq is alpha-equivalence. Use Expr.equal explicitly to bind
  -- every type/body, including binder names and annotations, to serialization.
  metadataEqual a b && a.type.equal b.type &&
    match a, b with
    | .defnInfo a, .defnInfo b => a.value.equal b.value
    | .thmInfo a, .thmInfo b => a.value.equal b.value
    | .opaqueInfo a, .opaqueInfo b => a.value.equal b.value
    | .recInfo a, .recInfo b =>
      (a.rules.zip b.rules).all (fun (a, b) => a.rhs.equal b.rhs)
    | .axiomInfo _, .axiomInfo _ | .quotInfo _, .quotInfo _ |
      .inductInfo _, .inductInfo _ | .ctorInfo _, .ctorInfo _ => true
    | _, _ => false

private def validateSerializedData (environment : Environment) (label : String)
    (data : ModuleData) : IO Unit := do
  unless data.isModule == environment.header.isModule && data.imports == environment.header.imports do
    oracleFailure "environment_delta_mismatch" s!"serialized {label} header differs from frontend"
  unless data.constNames == data.constants.map (·.name) do
    oracleFailure "environment_delta_mismatch" s!"serialized {label} constant-name index differs"
  unless (uniqueNames data.constNames).size == data.constNames.size do
    oracleFailure "environment_delta_mismatch" s!"serialized {label} has duplicate constant names"
  unless (uniqueNames (data.entries.map (·.1))).size == data.entries.size do
    oracleFailure "environment_delta_mismatch" s!"serialized {label} has duplicate extension names"

private def readSerializedFamily (environment : Environment) (path : System.FilePath) :
    IO SerializedFamily := do
  let names := if environment.header.isModule then
    #[path, path.withExtension "olean.server", path.withExtension "olean.private"] else #[path]
  let parts ← readModuleDataParts names
  unless parts.size == names.size do
    oracleFailure "environment_delta_mismatch" "serialized module view count differs"
  let data := parts.map (·.1)
  for i in [:data.size] do
    validateSerializedData environment s!"olean view {i}" data[i]!
  let ir? ← if environment.header.isModule then do
      let ir ← readModuleData (path.withExtension "ir")
      validateSerializedData environment "IR" ir.1
      unless ir.1.constants.isEmpty && ir.1.constNames.isEmpty do
        oracleFailure "environment_delta_mismatch" "serialized IR unexpectedly contains constants"
      pure (some ir)
    else pure none
  -- Regions are kept in the result and never explicitly freed while data is in
  -- use. Loading data does not import modules or execute their initializers.
  return { parts := data, regions := parts.map (·.2), ir? }

private def bindSerializedPrivate (environment : Environment) (data : ModuleData) :
    IO (Array ConstantInfo) := do
  let expected := environment.toKernelEnv.constants.foldStage2 (fun values _ info => values.push info) #[]
    |>.qsort (fun a b => a.name.toString < b.name.toString)
  let actual := data.constants.qsort (fun a b => a.name.toString < b.name.toString)
  unless expected.size == actual.size do
    oracleFailure "environment_delta_mismatch" "serialized private checked-domain count differs"
  for (a, b) in expected.zip actual do
    unless exactConstantInfo a b do
      oracleFailure "environment_delta_mismatch" s!"serialized private constant differs: {a.name}"
  return actual.filter (fun info => !environment.isImportedConst info.name)

private unsafe def serializedLCNF (data : ModuleData) (name : Name) :
    IO (Compiler.LCNF.DeclExtState .pure) := do
  let values : Array (Compiler.LCNF.Decl .pure) := unsafeCast
    ((data.entries.find? (·.1 == name)).map (·.2) |>.getD #[])
  let mut result := {}
  for value in values do
    if result.contains value.name then
      oracleFailure "environment_delta_mismatch" s!"duplicate serialized LCNF name: {value.name}"
    result := result.insert value.name value
  return result

private unsafe def compareSerializedMetadata (stock applied : Environment)
    (stockData appliedData : ModuleData) (label : String) : IO Unit := do
  unless stockData.isModule == appliedData.isModule do
    oracleFailure "environment_delta_mismatch" s!"serialized {label} module mode differs"
  -- Each view's imports were bound exactly to its own raw frontend header.
  compareDirectImports stock applied
  unless stockData.extraConstNames == appliedData.extraConstNames do
    oracleFailure "environment_delta_mismatch" s!"serialized {label} extraConstNames differ"
  for name in #[`Lean.Compiler.LCNF.baseExt, `Lean.Compiler.LCNF.monoExt] do
    compareLCNFDeclState s!"serialized {label} {name}"
      (← serializedLCNF stockData name) (← serializedLCNF appliedData name)
  compareModuleDocs stockData appliedData
  compareExtensions stock applied stockData appliedData
  compareExtraModUses stockData appliedData

private unsafe def observableSerializedInterface (environment : Environment)
    (declarations : Array ConstantInfo) : IO (Array ConstantInfo) := do
  let mut result := #[]
  for info in declarations do
    let some original := environment.toKernelEnv.constants.find? info.name
      | oracleFailure "environment_delta_mismatch" s!"serialized interface has no checked owner: {info.name}"
    -- Exported theorem interfaces may be axioms. Only the corresponding bound
    -- private declaration can justify the existing private-proof omission rule.
    unless ← privateProofDeclaration environment original do
      result := result.push info
  return result.qsort (fun a b => a.name.toString < b.name.toString)

private unsafe def compareSerializedFamilies (stock applied : Environment)
    (stockFamily appliedFamily : SerializedFamily) : IO Unit := do
  unless stockFamily.parts.size == appliedFamily.parts.size do
    oracleFailure "environment_delta_mismatch" "serialized family view counts differ"
  for i in [:stockFamily.parts.size] do
    let stockData := stockFamily.parts[i]!
    let appliedData := appliedFamily.parts[i]!
    compareSerializedMetadata stock applied stockData appliedData s!"view {i}"
    let stockInterface ← observableSerializedInterface stock stockData.constants
    let appliedInterface ← observableSerializedInterface applied appliedData.constants
    checkAppliedExpressions appliedInterface
    let _ ← checkDeclarationSets stock applied stockInterface appliedInterface {}
  match stockFamily.ir?, appliedFamily.ir? with
  | some stockIR, some appliedIR =>
    compareSerializedMetadata stock applied stockIR.1 appliedIR.1 "IR"
  | none, none => pure ()
  | _, _ => oracleFailure "environment_delta_mismatch" "serialized IR family presence differs"

private unsafe def runOracle (moduleName : Name) (stockPath appliedPath : System.FilePath)
    (oleanFileName? : Option System.FilePath := none)
    (stockOleanFileName? : Option System.FilePath := none) : IO OracleResult := do
  -- This is only a lexical distinctness guard. The caller must allocate fresh,
  -- canonical, nonoverlapping output families outside every import root.
  if let some stockOutput := stockOleanFileName? then
    unless oleanFileName?.isSome && oleanFileName? != some stockOutput do
      throw <| IO.userError "oracle_bridge_requires_distinct_output_paths"
  if oleanFileName?.isSome then
    unless (← IO.getEnv CommandAudit.enabledVariable) == some "1" do
      throw <| IO.userError "oracle_output_requires_command_audit"
    let _ ← CommandAudit.runNonce
  runExtensionNameSelfTest
  runLCNFComparatorSelfTest
  let (stock, applied) ← if stockOleanFileName?.isSome then do
      -- This separate bridge mode preserves the cold replay context: normal
      -- stock output would otherwise warm exporter caches before replay.
      -- Both families must independently match cold compiler outputs before
      -- a caller can claim fresh-compilation equivalence.
      let applied ← elaborateSource moduleName "applied" appliedPath oleanFileName?
      validateFrontendEnvironment applied
      let stock ← elaborateSource moduleName "stock" stockPath stockOleanFileName?
      validateFrontendEnvironment stock
      pure (stock, applied)
    else do
      let stock ← elaborateSource moduleName "stock" stockPath
      validateFrontendEnvironment stock
      let applied ← elaborateSource moduleName "applied" appliedPath oleanFileName?
      validateFrontendEnvironment applied
      pure (stock, applied)
  let serialized? ← match stockOleanFileName?, oleanFileName? with
    | some stockPath, some appliedPath =>
      pure <| some (← readSerializedFamily stock stockPath, ← readSerializedFamily applied appliedPath)
    | _, _ => pure none
  let (stockDeclarations, appliedDeclarations) ← match serialized? with
    | some (stockFamily, appliedFamily) => do
      pure (← bindSerializedPrivate stock stockFamily.parts.back!,
        ← bindSerializedPrivate applied appliedFamily.parts.back!)
    | none => pure (← sortedCurrentDeclarations stock, ← sortedCurrentDeclarations applied)
  let counts : OracleCounts := {
    stockDeclarations := stockDeclarations.size
    appliedDeclarations := appliedDeclarations.size
  }
  checkAppliedExpressions appliedDeclarations
  let counts ← checkDeclarationSets stock applied stockDeclarations appliedDeclarations counts
  checkAxiomSubset stock applied stockDeclarations appliedDeclarations
  let (stockData, appliedData) ← match serialized? with
    | some (stockFamily, appliedFamily) => do
      compareSerializedFamilies stock applied stockFamily appliedFamily
      pure (stockFamily.parts.back!, appliedFamily.parts.back!)
    | none => do
      let stockData ← Lean.mkModuleData stock
      let appliedData ← Lean.mkModuleData applied
      compareEnvironment stock applied stockData appliedData
      pure (stockData, appliedData)
  let counts := { counts with
    stockExtensions := stockData.entries.size
    appliedExtensions := appliedData.entries.size }
  return { counts }

private def resultJson (moduleName : Name) (result : OracleResult) : Json :=
  let c := result.counts
  Json.mkObj [
    ("kind", "simp_engine_declaration_oracle"),
    ("schema", 1),
    ("module", moduleName.toString),
    ("status", "success"),
    ("failureCategory", Json.null),
    ("failureDetail", Json.null),
    ("stockDeclarationCount", c.stockDeclarations),
    ("appliedDeclarationCount", c.appliedDeclarations),
    ("commonPublicDeclarationCount", c.commonPublicDeclarations),
    ("stockOnlyPrivateProofCount", c.stockOnlyPrivateProof),
    ("appliedOnlyPrivateProofCount", c.appliedOnlyPrivateProof),
    ("stockExtensionCount", c.stockExtensions),
    ("appliedExtensionCount", c.appliedExtensions),
    ("checkedDeclarationCount", c.checkedDeclarations)
  ]

private def failureCategory (message : String) : String :=
  let marker := "DECLARATION_ORACLE_FAILURE|"
  match message.splitOn marker with
  | _ :: rest :: _ =>
      match rest.splitOn "|" with
      | category :: _ => category
      | _ => "environment_delta_mismatch"
  | _ => "environment_delta_mismatch"

private def failureDetail (message : String) : String :=
  let marker := "DECLARATION_ORACLE_FAILURE|"
  match message.splitOn marker with
  | _ :: rest :: _ =>
      match rest.splitOn "|" with
      | _ :: detail :: _ => detail
      | _ => message
  | _ => message

private def failureJson (moduleName : Name) (category detail : String) : Json :=
  Json.mkObj [
    ("kind", "simp_engine_declaration_oracle"),
    ("schema", 1),
    ("module", moduleName.toString),
    ("status", "failure"),
    ("failureCategory", category),
    ("failureDetail", detail),
    ("stockDeclarationCount", 0),
    ("appliedDeclarationCount", 0),
    ("commonPublicDeclarationCount", 0),
    ("stockOnlyPrivateProofCount", 0),
    ("appliedOnlyPrivateProofCount", 0),
    ("stockExtensionCount", 0),
    ("appliedExtensionCount", 0),
    ("checkedDeclarationCount", 0)
  ]

unsafe def _root_.main (args : List String) : IO UInt32 := do
  let some (moduleName, stockPath, appliedPath, oleanFileName?, stockOleanFileName?) := (match args with
    | [moduleName, stockPath, appliedPath] => some (moduleName, stockPath, appliedPath, none, none)
    | [moduleName, stockPath, appliedPath, "--olean", output] =>
      some (moduleName, stockPath, appliedPath, some (System.FilePath.mk output), none)
    | [moduleName, stockPath, appliedPath, "--bridge-oleans", stockOutput, appliedOutput] =>
      some (moduleName, stockPath, appliedPath, some (System.FilePath.mk appliedOutput),
        some (System.FilePath.mk stockOutput))
    | _ => none)
    | IO.eprintln "usage: SimpEngineDeclarationOracle.lean <module> <stock.lean> <applied.lean> [--olean applied.olean | --bridge-oleans stock.olean applied.olean]" *>
      pure 2
  let marker := if stockOleanFileName?.isSome then "SIMP_ENGINE_COLD_BRIDGE_ORACLE_V2"
    else "SIMP_ENGINE_DECLARATION_ORACLE"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  -- Bridge framing contract v2: serialized emitted data, no comparison exports; validated run nonce followed by the unchanged
  -- schema-1 oracle payload. Its command-audit order is applied, then stock.
  let bridgeNonce? ← if stockOleanFileName?.isSome then
      try pure <| some (← CommandAudit.runNonce)
      catch _ => pure none
    else pure none
  let emitResult := fun (payload : Json) => do
    if stockOleanFileName?.isSome then
      let some nonce := bridgeNonce?
        | IO.eprintln "cold bridge result unavailable without a valid run nonce"
      -- Export callbacks may have printed a partial line after the last audit.
      IO.println s!"\n{marker} {nonce} {payload.compress}"
    else
      IO.println s!"{marker} {payload.compress}"
  try
    let result ← runOracle moduleName.toName stockPath appliedPath oleanFileName? stockOleanFileName?
    emitResult (resultJson moduleName.toName result)
    pure 0
  catch error =>
    let message := error.toString
    let category := failureCategory message
    let detail := failureDetail message
    emitResult (failureJson moduleName.toName category detail)
    pure 1

end ExplicitLean.SimpEngine.DeclarationOracle
