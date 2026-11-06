import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.SphereSobolevZeroSectionSupport
import Calderon.RealNormedGroupProjectionData

/-! Preparation of the original native mixed J section. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceNativeMovingAdjointParametricJ
  sphereSobolevInclusionL sphereSobolevZeroEquiv

lemma contDiff_referenceNativeMovingAdjointParametricJ_fderiv
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (fun y : R3 =>
      referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),fderiv ℝ R y)) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_MIXED_J_PREPARATION PARAMETER_BODY"
    out.flush
  have hDR : ContDiff ℝ ∞ (fderiv ℝ R) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    exact hR.contDiffAt.fderiv_right (by simp)
  have hParam : ContDiff ℝ ∞ (fun y : R3 => ((q,y),fderiv ℝ R y)) :=
    (contDiff_const.prodMk contDiff_id).prodMk hDR
  exact (contDiff_referenceNativeMovingAdjointParametricJ hF hO hD g g2 hg hg2 L).comp hParam

lemma referenceNativeMovingAdjointParametricJ_lift_smooth_compact
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) :
    let I31 := sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
    let U : R3 → SphereSobolev 1 := fun y => I31 (u y)
    let T : R3 → SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
      fun y => referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),fderiv ℝ R y)
    let Z := sphereSobolevZeroEquiv hO hD
    let j : R3 → SphereL2 := fun y => Z.symm (T y (U y))
    ContDiff ℝ ∞ U ∧ tsupport U ⊆ tsupport u ∧ HasCompactSupport U ∧
      ContDiff ℝ ∞ j ∧ tsupport j ⊆ tsupport u ∧ HasCompactSupport j ∧
      MemLp j 2 (volume : Measure R3) := by
  intro I31 U T Z j
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_MIXED_J_PREPARATION SECTION_BODY"
    out.flush
  have hU : ContDiff ℝ ∞ U := I31.contDiff.comp hu
  have hT : ContDiff ℝ ∞ T :=
    contDiff_referenceNativeMovingAdjointParametricJ_fderiv hF hO hD g g2 hg hg2 L q R hR
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_MIXED_J_PREPARATION OPERATOR_SMOOTH_READY"
    out.flush
  have hj : ContDiff ℝ ∞ j :=
    Z.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp (hT.clm_apply hU)
  have hUSupport : tsupport U ⊆ tsupport u := by
    apply closure_minimal ?_ (isClosed_tsupport u)
    intro y hy
    by_contra hOutside
    have hu0 : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
    exact hy ((congrArg I31 hu0).trans (ContinuousLinearMap.map_zero I31))
  have hCompositeSupport :=
    tsupport_sphereSobolevZeroEquiv_symm_clm_apply_subset hO hD T U
  have hjSupport : tsupport j ⊆ tsupport u := hCompositeSupport.trans hUSupport
  have hUCompact : HasCompactSupport U :=
    hcu.of_isClosed_subset (isClosed_tsupport U) hUSupport
  have hjCompact : HasCompactSupport j :=
    hcu.of_isClosed_subset (isClosed_tsupport j) hjSupport
  have hjMem : MemLp j 2 (volume : Measure R3) :=
    hj.continuous.memLp_of_hasCompactSupport hjCompact
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_MIXED_J_PREPARATION SMOOTH_COMPACT_READY"
    out.flush
  exact ⟨hU,hUSupport,hUCompact,hj,hjSupport,hjCompact,hjMem⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNativeMovingAdjointParametricJ_fderiv
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointParametricJ_lift_smooth_compact
