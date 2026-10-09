Compilation is not verification. The EleutherAI/Cambridge audit of five Lean benchmarks (arXiv:2606.29493) found
4,833 defect findings across roughly 10,000 problems, including 199 axiom-injection instances concentrated in
DeepSeek's ProverBench: an unrestricted `axiom h : P` lets any solver "prove" P and the file compiles clean. The same
audit documents a Lean frontend bug before v4.20.0 in which `apply?` could introduce a synthetic `sorry` without the
usual warning, so three proofs claimed by DeepSeek-Prover-V2 reported success while the kernel never checked them. The
July–August 2026 Lean kernel soundness hunt found real kernel bugs: a kernel bug in nested-inductive handling let an
AI-assisted Collatz "disproof" pass, and the hunt it triggered fixed six kernel soundness bugs in v4.33.1. A pipeline
that treats exit status zero as verification passes every one of these.
