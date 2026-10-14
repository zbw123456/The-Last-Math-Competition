import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import SupportTree

noncomputable section
namespace SparseBackward
/-- Coordinates of an actual real 2-by-2 matrix. -/
structure Mat where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def normSq (E : Mat) : ℝ := E.a^2 + E.b^2 + E.c^2 + E.d^2
def matrixA : Mat := ⟨1,1,0,1⟩
def entry (M : Mat) (i j : Fin 2) : ℝ :=
  if i=0 then (if j=0 then M.a else M.b) else (if j=0 then M.c else M.d)
def mulOnes (M : Mat) : ℝ × ℝ := (M.a+M.b,M.c+M.d)
def add (A E : Mat) : Mat := ⟨A.a+E.a,A.b+E.b,A.c+E.c,A.d+E.d⟩
/-- x=(1,1), b=(3,2), and (A+E)x=b. Only A is perturbed. -/
def Feasible (E : Mat) : Prop := mulOnes (add matrixA E) = (3,2)
def Supported (E : Mat) : Prop := E.c=0
/-- Orthogonal coordinate projection onto the support of A. -/
def project (E : Mat) : Mat := ⟨E.a,E.b,0,E.d⟩
def dense : Mat := ⟨1/2,1/2,1/2,1/2⟩
def sparse : Mat := ⟨1/2,1/2,0,1⟩
def DenseMinimum (E : Mat) : Prop := Feasible E ∧
  ∀ F : Mat, Feasible F → normSq E ≤ normSq F
def SparseMinimum (E : Mat) : Prop := Feasible E ∧ Supported E ∧
  ∀ F : Mat, Feasible F → Supported F → normSq E ≤ normSq F

theorem feasible_iff (E : Mat) : Feasible E ↔ E.a+E.b=1 ∧ E.c+E.d=1 := by
  simp only [Feasible,mulOnes,add,matrixA,Prod.mk.injEq]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem dense_value : normSq dense=1 := by norm_num [normSq,dense]
theorem sparse_value : normSq sparse=3/2 := by norm_num [normSq,sparse]

theorem dense_is_minimum : DenseMinimum dense := by
  constructor
  · rw [feasible_iff]; norm_num [dense]
  · intro F hF
    rw [feasible_iff] at hF
    rw [dense_value]
    unfold normSq
    nlinarith [sq_nonneg (F.a-F.b),sq_nonneg (F.c-F.d)]

theorem sparse_is_minimum : SparseMinimum sparse := by
  refine ⟨?_,rfl,?_⟩
  · rw [feasible_iff]; norm_num [sparse]
  · intro F hF hS
    rw [feasible_iff] at hF
    change F.c=0 at hS
    rw [sparse_value]
    unfold normSq
    nlinarith [sq_nonneg (F.a-F.b)]

theorem projection_not_feasible : ¬ Feasible (project dense) := by
  rw [feasible_iff]
  norm_num [project,dense]

theorem every_dense_minimum_is_dense (E : Mat) (h : DenseMinimum E) : E=dense := by
  have hf := (feasible_iff E).mp h.1
  have hn := h.2 dense dense_is_minimum.1
  rw [dense_value] at hn
  unfold normSq at hn
  have h1 := sq_nonneg (E.a-E.b)
  have h2 := sq_nonneg (E.c-E.d)
  have hab : E.a=E.b := by nlinarith [sq_nonneg (E.c+E.d)]
  have hcd : E.c=E.d := by nlinarith [sq_nonneg (E.a+E.b)]
  have ha : E.a=1/2 := by linarith
  have hb : E.b=1/2 := by linarith
  have hc : E.c=1/2 := by linarith
  have hd : E.d=1/2 := by linarith
  cases E
  simp_all [dense]

/-- Every dense minimizer fails after support projection, not merely a
poorly chosen nonminimal dense perturbation. -/
theorem no_projected_dense_minimizer :
    ∀ E : Mat, DenseMinimum E → ¬ SparseMinimum (project E) := by
  intro E h
  rw [every_dense_minimum_is_dense E h]
  intro hs
  exact projection_not_feasible hs.1

theorem counterexample : DenseMinimum dense ∧ SparseMinimum sparse ∧
    ¬ Feasible (project dense) ∧ normSq dense < normSq sparse := by
  refine ⟨dense_is_minimum,sparse_is_minimum,projection_not_feasible,?_⟩
  rw [dense_value,sparse_value]
  norm_num

theorem support_correspondence (i j : Fin 2) :
    SupportTree.supportGraph.Adj (SupportTree.rowVertex i) (SupportTree.colVertex j) ↔
      entry matrixA i j ≠ 0 := by
  rw [SupportTree.support_correspondence]
  fin_cases i <;> fin_cases j <;> norm_num [entry,matrixA,SupportTree.entry]

theorem counterexample_with_tree : SupportTree.supportGraph.IsTree ∧
    (∀ i j : Fin 2,
      SupportTree.supportGraph.Adj (SupportTree.rowVertex i) (SupportTree.colVertex j) ↔
        entry matrixA i j ≠ 0) ∧
    DenseMinimum dense ∧ SparseMinimum sparse ∧ ¬ Feasible (project dense) :=
  ⟨SupportTree.tree,support_correspondence,dense_is_minimum,sparse_is_minimum,
    projection_not_feasible⟩

/-- A support-aware row correction succeeds for this same example.
This is why failure of raw projection does not refute an unspecified
normalized conversion formula. -/
def normalizedProject (E : Mat) : Mat := ⟨E.a,E.b,0,2*E.d⟩

theorem normalized_projection_recovers_sparse : normalizedProject dense = sparse := by
  unfold normalizedProject dense sparse
  norm_num

theorem normalized_projection_is_minimum : SparseMinimum (normalizedProject dense) := by
  rw [normalized_projection_recovers_sparse]
  exact sparse_is_minimum

#print axioms normalized_projection_is_minimum
#print axioms counterexample
#print axioms no_projected_dense_minimizer
#print axioms counterexample_with_tree
end SparseBackward
