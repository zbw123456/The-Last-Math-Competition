AUDIT CORRECTION (14 October 2026): RESEARCH ONLY -- NOT A COMPLETE DISPROOF.
This file supersedes the previous candidate status. Do not submit as a solution.
The direct coordinate projection fails, but the original question does not
specify that conversion. A row-normalized support projection recovers the
sparse minimum in this very example, as normalized_projection_is_minimum now
proves. This item is excluded from the completed-solution count and PR drafts.

Conjecture 00000005137: review candidate, not an accepted competition solution.

Scope
Uses matrix-only backward error for Ax=b, the Frobenius norm, and coordinate
support projection. The original problem does not specify the norm, whether
b may also be perturbed, or a precise alternative conversion formula. Under
this standard concrete reading the projection fails even feasibility.
Real 2-by-2 matrices, the actual residual equation, squared Frobenius objective,
all competing real perturbations, dense and sparse minima, and uniqueness of
the dense minimizer are formalized. SupportTree.lean proves Mathlib SimpleGraph.IsTree for the support graph;
SparseBackward.support_correspondence checks each actual matrix entry.

Reproduction
Install Lean 4.19.0 through elan. In lean/, run lake build, then
lake env lean -DwarningAsError=true SparseBackward.lean.
Mathlib is pinned to commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
On a fresh checkout, lake update and lake exe cache get may obtain dependencies.
The manifest fixes every dependency. The local audit used the official cache
via lake env lean --run Cache/Main.lean because the generated cache executable
had a macOS dynamic-loader compatibility failure; no proof checking was bypassed.

With pdflatex available, sh verify.sh also compiles the report twice.
No proof placeholders, native_decide, or custom axiom declarations are used.
Only standard Lean foundations occur in the axiom audit.

Publication
Prepared locally for review. No PR or Issue was created. Official metadata
and historical/open PR evidence are recorded in the separate batch audit.
