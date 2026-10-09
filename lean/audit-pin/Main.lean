import Audit
open Lean

instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

/-- A constant's name as the checker prints it; numeric components (a private name's) are numbers. -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n p => match p.toNat? with | some k => .num n k | none => .str n p) .anonymous

/-- The steps from `src` to `dst` along the uses of constants of module `own`, or none when `dst` is not reached. -/
def distance (env : Environment) (own src dst : Name) : Option Nat := Id.run do
  let mut frontier := #[src]
  let mut seen : NameSet := ({} : NameSet).insert src
  let mut d := 0
  while !frontier.isEmpty do
    if frontier.contains dst then return some d
    let mut next := #[]
    for n in frontier do
      for u in Audit.uses env n do
        if !seen.contains u && (Audit.moduleOf env own u).isNone then
          seen := seen.insert u
          next := next.push u
    frontier := next
    d := d + 1
  return none

/-- The member whose uses reach `c`, a constant of module `own`, in the fewest steps, or why there is none. -/
def walk (env : Environment) (own c : Name) (members : List Name) : Json :=
  let none_ (reason : String) := Json.mkObj [("member", .null), ("reason", reason)]
  if (env.find? c).isNone then none_ "none"
  else if (Audit.moduleOf env own c).isSome then none_ "imported"
  else
    let found := members.filterMap fun m => (distance env own m c).map (·, m)
    match (found.map (·.1)).min? with
    | none => none_ "none"
    | some d => match found.filter (·.1 == d) with
      | [(_, m)] => Json.mkObj [("member", Audit.str m)]
      | _ => none_ "tie"

/-- The audit with this toolchain's collector, `Lean.collectAxioms`; and
`ledger-audit walk --module M --constant C --members-file F`, F listing the members one per line (lines starting
`#` skipped), which prints the member nearest C in M's dependency graph, or null and why. -/
def main : List String → IO UInt32
  | ["walk", "--module", m, "--constant", c, "--members-file", f] => do
    try
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := m.toName }] {}
      let members := (← IO.FS.lines f).toList.filter (fun l => !l.isEmpty && !l.startsWith "#")
      IO.println (walk env m.toName (parseName c) (members.map String.toName)).compress
      return 0
    catch e =>
      IO.eprintln e
      return 1
  | args => Audit.main (fun env d => (collectAxioms d : StateM Environment (Array Name)).run' env) args
