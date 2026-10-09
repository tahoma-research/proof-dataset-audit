import Lake
open Lake DSL

package audit

lean_lib Audit

@[default_target]
lean_exe audit where
  root := `Main
  exeName := "ledger-audit"
  supportInterpreter := true
