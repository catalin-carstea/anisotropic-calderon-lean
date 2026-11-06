import Calderon.ActualFramedPositiveMetric
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The cutoff support itself supplies positivity, so no larger q-room is assumed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError

private instance instCompleteNearIdentityR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

private instance instCompleteNearIdentityEnd : CompleteSpace (R3 →L[ℝ] R3) :=
  ContinuousLinearMap.instCompleteSpace

def nearIdentityOperatorBump : ContDiffBump (ContinuousLinearMap.id ℝ R3) :=
  ⟨1/4,1/2,by norm_num,by norm_num⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def nearIdentityPositiveMatrixExtension (G : P → R3 →L[ℝ] R3)
    (p : P) : Matrix (Fin 3) (Fin 3) ℝ :=
  nearIdentityOperatorBump (G p) • operatorMatrixMap (G p) +
    (1-nearIdentityOperatorBump (G p)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

theorem contDiff_nearIdentityPositiveMatrixExtension (G : P → R3 →L[ℝ] R3)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (nearIdentityPositiveMatrixExtension G) := by
  have hb := nearIdentityOperatorBump.contDiff.comp hG
  exact (hb.smul (operatorMatrixMap.contDiff.comp hG)).add
    ((contDiff_const.sub hb).smul contDiff_const)

theorem nearIdentityPositiveMatrixExtension_eq (G : P → R3 →L[ℝ] R3)
    (p : P) (hp : ‖G p-ContinuousLinearMap.id ℝ R3‖ ≤ (1/4 : ℝ)) :
    nearIdentityPositiveMatrixExtension G p = operatorMatrixMap (G p) := by
  have hb : nearIdentityOperatorBump (G p) = 1 := by
    apply nearIdentityOperatorBump.one_of_mem_closedBall
    simpa only [nearIdentityOperatorBump,mem_closedBall,dist_eq_norm] using hp
  simp [nearIdentityPositiveMatrixExtension,hb]

theorem nearIdentityPositiveMatrixExtension_posDef (G : P → R3 →L[ℝ] R3)
    (hsym : ∀ p u v, inner ℝ (G p u) v = inner ℝ (G p v) u) (p : P) :
    (nearIdentityPositiveMatrixExtension G p).PosDef := by
  by_cases hz : nearIdentityOperatorBump (G p) = 0
  · simpa [nearIdentityPositiveMatrixExtension,hz] using
      (Matrix.PosDef.one : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef)
  have hb0 : 0 ≤ nearIdentityOperatorBump (G p) := nearIdentityOperatorBump.nonneg' (G p)
  have hb1 : nearIdentityOperatorBump (G p) ≤ 1 := nearIdentityOperatorBump.le_one
  have hbpos : 0 < nearIdentityOperatorBump (G p) := lt_of_le_of_ne hb0 (Ne.symm hz)
  have hm : G p ∈ Function.support nearIdentityOperatorBump := hz
  have hn : ‖G p-ContinuousLinearMap.id ℝ R3‖ < (1/2 : ℝ) := by
    simpa only [ContDiffBump.support_eq,nearIdentityOperatorBump,mem_ball,dist_eq_norm] using hm
  have hGP : (operatorMatrixMap (G p)).PosDef := by
    apply operatorMatrixMap_posDef _ (hsym p)
    intro u hu
    exact lt_of_lt_of_le
      (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hu)))
      (inner_lower_bound_of_norm_sub_id_le_half _ hn.le u)
  exact (hGP.smul hbpos).add_posSemidef
    (Matrix.PosDef.one.posSemidef.smul (sub_nonneg.mpr hb1))

end OAI.AnisotropicCalderon.MetricOperator
