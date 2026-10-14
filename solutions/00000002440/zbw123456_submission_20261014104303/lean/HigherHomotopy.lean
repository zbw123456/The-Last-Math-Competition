import Mathlib.Topology.Homotopy.HomotopyGroup

/-! Conjecture 00000002440. The third homotopy group of every stage of
any pointed homotopy pro-system is abelian. Compatible inverse-limit
families are also abelian. No assumption about the first group is needed. -/
noncomputable section
namespace HigherHomotopy
open scoped Topology
universe u v

theorem pi3_comm (X : Type u) [TopologicalSpace X] (x : X)
    (a b : π_ 3 X x) : a * b = b * a := mul_comm a b

variable {ι : Type v} [Preorder ι] (X : ι → Type u)
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)

/- Commutativity holds levelwise, hence the pro-group takes values in
abelian groups for every representing diagram. -/
omit [Preorder ι] in
theorem every_stage_abelian :
    ∀ i, ∀ a b : π_ 3 (X i) (x i), a * b = b * a :=
  fun i => pi3_comm (X i) (x i)

/-- Compatible families for arbitrary bonding homomorphisms. The usual
inverse-system identity/composition laws may be imposed, but are not
needed for commutativity. -/
def compatibleFamilies
    (bond : ∀ i j, i ≤ j → (π_ 3 (X j) (x j)) →* (π_ 3 (X i) (x i))) :
    Subgroup (∀ i, π_ 3 (X i) (x i)) where
  carrier := {a | ∀ i j h, bond i j h (a j) = a i}
  one_mem' := by intro i j h; exact (bond i j h).map_one
  mul_mem' := by
    intro a b ha hb i j h
    change bond i j h (a j * b j) = a i * b i
    rw [map_mul, ha i j h, hb i j h]
  inv_mem' := by
    intro a ha i j h
    change bond i j h (a j)⁻¹ = (a i)⁻¹
    rw [map_inv, ha i j h]

theorem limit_abelian
    (bond : ∀ i j, i ≤ j → (π_ 3 (X j) (x j)) →* (π_ 3 (X i) (x i)))
    (a b : compatibleFamilies X x bond) : a * b = b * a := mul_comm a b

omit [Preorder ι] in
theorem no_nonabelian_pi3 :
    ¬ ∃ i, ∃ a b : π_ 3 (X i) (x i), a * b ≠ b * a := by
  rintro ⟨i, a, b, h⟩
  exact h (pi3_comm (X i) (x i) a b)

#print axioms no_nonabelian_pi3
#print axioms limit_abelian
end HigherHomotopy
