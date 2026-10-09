import Audit
open Lean Elab Command

/-- The audit with this toolchain's collector, `CollectAxioms.collect`. -/
def main (args : List String) : IO UInt32 :=
  Audit.main (fun env d => (((CollectAxioms.collect d).run env).run {}).2.axioms) args
