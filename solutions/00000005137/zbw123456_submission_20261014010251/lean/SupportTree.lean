import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

namespace SupportTree
def supportGraph : SimpleGraph (Fin 4) := SimpleGraph.pathGraph 4
instance : DecidableRel supportGraph.Adj := fun i j =>
  decidable_of_iff (i.val+1=j.val ∨ j.val+1=i.val) SimpleGraph.pathGraph_adj.symm

theorem tree : supportGraph.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨SimpleGraph.pathGraph_connected 3, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [← SimpleGraph.edgeFinset_card]
  decide

def rowVertex (i : Fin 2) : Fin 4 := if i=0 then 1 else 3
def colVertex (j : Fin 2) : Fin 4 := if j=0 then 0 else 2
def entry (i j : Fin 2) : ℝ := if i=1 ∧ j=0 then 0 else 1

theorem support_correspondence (i j : Fin 2) :
    supportGraph.Adj (rowVertex i) (colVertex j) ↔ entry i j ≠ 0 := by
  rw [show supportGraph=SimpleGraph.pathGraph 4 from rfl,
    SimpleGraph.pathGraph_adj]
  fin_cases i <;> fin_cases j <;> norm_num [rowVertex,colVertex,entry] <;> decide

#print axioms tree
#print axioms support_correspondence
end SupportTree
