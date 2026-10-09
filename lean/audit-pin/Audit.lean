import Lean
open Lean

/-! The axiom audit shared by both toolchains' `ledger-audit`; each toolchain's Main supplies its collector.

`ledger-audit audit --module M --decl D [--decl D ...] [--own-module O]` imports M and prints, for each D, one
JSON line: the axioms the collector reports, the axioms an independent walk reaches, each with its declaring
module (null: declared in O, by default M) and whether a constant of O uses it directly, and the hash and text
of D's type. Any failure prints its message on stderr and exits 1. -/

namespace Audit

/-- The module declaring `c`, or none when that module is `own`. -/
def moduleOf (env : Environment) (own c : Name) : Option Name := do
  let m := env.header.moduleNames[(← env.getModuleIdxFor? c).toNat]!
  if m == own then none else some m

/-- The constants in `c`'s type and value, an inductive's constructors, and an inductive's recursor, which
nothing there names. -/
def uses (env : Environment) (c : Name) : NameSet :=
  match env.find? c with
  | some ci@(.inductInfo _) => ci.getUsedConstantsAsSet.insert (mkRecName c)
  | some ci => ci.getUsedConstantsAsSet
  | none => {}

/-- The walk's memo, kept across declarations: the axioms reachable from each constant whose strongly
connected component is finished; and, for the component being explored, Tarjan's preorder index and stack. -/
structure Walk where
  axioms : NameMap NameSet := {}
  index : NameMap Nat := {}
  stack : Array Name := #[]
  next : Nat := 0

/-- The axioms reachable from `c` through types and values, axioms' types included, and the lowest index of a
constant on the stack that `c` reaches. Constants of one cycle reach the same constants, so the cycle's root
records its whole set for every member when it finishes; no partial set is ever memoised. -/
partial def walk (env : Environment) (c : Name) : StateM Walk (NameSet × Nat) := do
  let s ← get
  if let some axs := s.axioms.find? c then return (axs, s.next)
  if let some i := s.index.find? c then return ({}, i)
  let i := s.next
  set { s with index := s.index.insert c i, stack := s.stack.push c, next := i + 1 }
  let mut axs : NameSet := if env.find? c matches some (.axiomInfo _) then ({} : NameSet).insert c else {}
  let mut low := i
  for d in uses env c do
    let (a, l) ← walk env d
    axs := axs ++ a
    low := min low l
  if low == i then
    let mut s ← get
    repeat
      let top := s.stack[s.stack.size - 1]!
      s := { s with stack := s.stack.pop, index := s.index.erase top, axioms := s.axioms.insert top axs }
      if top == c then break
    set s
  return (axs, low)

/-- The constants of module `own` reachable from `todo`. -/
partial def ownClosure (env : Environment) (own : Name) : List Name → NameSet → NameSet
  | [], seen => seen
  | c :: todo, seen =>
    if seen.contains c || (moduleOf env own c).isSome then ownClosure env own todo seen
    else ownClosure env own ((uses env c).toList ++ todo) (seen.insert c)

def str (n : Name) : Json := .str (n.toString (escape := false))

def axiomJson (env : Environment) (own n : Name) : Json :=
  Json.mkObj [("name", str n), ("module", ((moduleOf env own n).map str).getD .null)]

/-- One declaration's line, and the walk's memo for the next. -/
def audit (collect : Environment → Name → Array Name) (env : Environment) (own d : Name) (memo : Walk) :
    IO (Json × Walk) := do
  let some ci := env.find? d | throw (IO.userError s!"{d} is not declared in the imported environment")
  let t0 ← IO.monoNanosNow
  let collected ← IO.lazyPure fun _ => collect env d
  let t1 ← IO.monoNanosNow
  let ((axs, _), memo) ← IO.lazyPure fun _ => (walk env d).run memo
  -- via_own: some constant of `own` reachable from d, d included, uses the axiom directly.
  let direct ← IO.lazyPure fun _ =>
    (ownClosure env own [d] {}).toList.foldl (fun acc o => acc ++ uses env o) ({} : NameSet)
  let t2 ← IO.monoNanosNow
  let entry := fun n => (axiomJson env own n).setObjVal! "via_own" (.bool (direct.contains n))
  return (Json.mkObj [("name", str d), ("axioms_collector", .arr (collected.map entry)),
    ("axioms_walk", .arr (axs.toList.map entry).toArray), ("type_hash", .str (toString ci.type.hash)),
    ("type_pp", .str (toString ci.type)), ("collector_us", toJson ((t1 - t0) / 1000)),
    ("walk_us", toJson ((t2 - t1) / 1000))], memo)

def main (collect : Environment → Name → Array Name) (args : List String) : IO UInt32 := do
  try
    let rec parse : List String → Name × Array Name × Option Name → IO (Name × Array Name × Option Name)
      | [], acc => pure acc
      | "--module" :: m :: rest, (_, ds, o) => parse rest (m.toName, ds, o)
      | "--decl" :: d :: rest, (m, ds, o) => parse rest (m, ds.push d.toName, o)
      | "--own-module" :: o :: rest, (m, ds, _) => parse rest (m, ds, some o.toName)
      | a :: _, _ => throw (IO.userError s!"unexpected argument {a}")
    -- With --skip-missing a declaration not in the environment prints no line instead of failing the audit.
    let skip := args.contains "--skip-missing"
    let (m, decls, own) ← match args.erase "--skip-missing" with
      | "audit" :: rest => parse rest (.anonymous, #[], none)
      | _ => throw (IO.userError
          "usage: ledger-audit audit [--skip-missing] --module M --decl D [--decl D ...] [--own-module O]")
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := m }] {}
    let mut memo : Walk := {}
    for d in decls do
      if skip && (env.find? d).isNone then continue
      let (line, next) ← audit collect env (own.getD m) d memo
      memo := next
      IO.println line.compress
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    return 1

end Audit
