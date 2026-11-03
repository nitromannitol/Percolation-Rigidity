import Lake
open Lake DSL

package «percolation-rigidity» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @
    "7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069"

/-- The formalization: every module under `Rigidity/`. A warning is an error. -/
@[default_target]
lean_lib Rigidity where
  globs := #[.andSubmodules `Rigidity]
  leanOptions := #[⟨`warningAsError, true⟩]

/-- The audit surface: the axiom report `RigidityAudit/Axioms.lean` and the comparator pairs
`RigidityAudit/*/Challenge.lean`, `RigidityAudit/*/Solution.lean`. Deliberately **not** a default
target: it builds only on demand (`lake build RigidityAudit`), so the ordinary build is unchanged;
each challenge elaborates with its one intentional `sorry`. -/
lean_lib RigidityAudit where
  globs := #[.submodules `RigidityAudit]
