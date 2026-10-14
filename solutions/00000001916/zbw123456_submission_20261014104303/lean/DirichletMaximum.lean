import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace DirichletMaximum
open Filter Asymptotics
open scoped BigOperators Topology

/-- n^(it)=exp(it log n), with n=1,...,N and all coefficients equal to one. -/
def dirichlet (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, Complex.exp ((t * Real.log (n + 1) : ℝ) * Complex.I)

theorem value_at_zero (N : ℕ) : dirichlet N 0 = N := by simp [dirichlet]

theorem norm_le (N : ℕ) (t : ℝ) : ‖dirichlet N t‖ ≤ N := by
  calc
    ‖dirichlet N t‖ ≤ ∑ n ∈ Finset.range N,
        ‖Complex.exp ((t * Real.log (n + 1) : ℝ) * Complex.I)‖ := norm_sum_le _ _
    _ = N := by simp [Complex.norm_exp]

/-- The supremum really is N, not merely at least N. -/
theorem maximum_exact (N : ℕ) : IsGreatest (Set.range (fun t => ‖dirichlet N t‖)) (N : ℝ) := by
  constructor
  · exact ⟨0, by simp [value_at_zero]⟩
  · rintro _ ⟨t, rfl⟩
    exact norm_le N t

def claimedScale (x : ℝ) : ℝ := x ^ (1 / 2 : ℝ) * Real.log (Real.log x) ^ (1 / 4 : ℝ)

theorem scale_littleO : claimedScale =o[atTop] (fun x : ℝ => x) := by
  have hb : (fun x : ℝ => Real.log (Real.log x) ^ (1 / 4 : ℝ)) =O[atTop]
      (fun x : ℝ => Real.log x ^ (1 / 4 : ℝ)) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    have he : Real.log (Real.log x) ^ (1 / 4 : ℝ) ≤ Real.log x ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg hx) (Real.log_le_self (by linarith)) (by norm_num)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) (1 / 4 : ℝ)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) (1 / 4 : ℝ))] using he
  have hl := hb.trans_isLittleO (isLittleO_log_rpow_rpow_atTop (1 / 4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2))
  have hp := hl.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ (1 / 2 : ℝ)) atTop)
  apply hp.congr'
  · exact Eventually.of_forall fun x => by simp [claimedScale, mul_comm]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    norm_num

theorem no_claimed_bound : ¬ (fun N : ℕ => (N : ℝ)) =O[atTop]
    (fun N : ℕ => claimedScale N) := by
  intro h
  have hl := h.trans_isLittleO (scale_littleO.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hb := hl.bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN, hp⟩ := ((eventually_ge_atTop 1).and hb).exists
  simp only [Function.comp_apply, Real.norm_natCast] at hp
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

#print axioms maximum_exact
#print axioms no_claimed_bound
end DirichletMaximum
