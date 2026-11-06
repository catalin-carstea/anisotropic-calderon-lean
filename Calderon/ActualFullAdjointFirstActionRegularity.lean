import Calderon.ActualFullAdjointFirstActions

/-! The same ordinary uncompressed Y. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighFullAdjointFirstAction
  referenceHighMovingBoundaryActionFamily referenceHighHorizontalAction
  sphereSobolevInclusionL referenceMetricGramFrame referenceFrameConnectionCoefficient

lemma contDiffAt_referenceHighFullAdjointFirstAction
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i) y := by
  have hHorizontal := contDiffAt_referenceHighHorizontalAction g hg L q u y i hu
  have hMoving := (contDiffAt_referenceHighMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hR hr hInv hStrong).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  have hBoundary := hMoving.clm_apply hu
  have hValue : ContDiffAt ℝ ∞ (fun x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x)) y :=
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).contDiff.contDiffAt.comp y hu
  have hDelta : ContDiffAt ℝ ∞ (fun x => ∑ a : Fin 3,
      referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) a) a i) y := by
    apply ContDiffAt.sum
    intro a ha
    exact (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun x => referenceMetricGramFrame g L (q,x) a)
      (contDiff_referenceMetricGramFrame_slice g hg L q a) a i).contDiffAt
  simpa only [referenceHighFullAdjointFirstAction,Function.comp_def,
    Pi.add_def,Pi.sub_def,Pi.neg_def,Pi.smul_def'] using
      ((hHorizontal.neg.add hBoundary).sub (hDelta.smul hValue))

lemma tsupport_referenceHighFullAdjointFirstAction_subset
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (i : Fin 3) :
    tsupport (fun y => referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) ⊆ tsupport u := by
  classical
  change closure (Function.support (fun y : R3 => referenceHighFullAdjointFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i)) ⊆ tsupport u
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hyu
  have hU : u y = 0 := image_eq_zero_of_notMem_tsupport hyu
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hyu
  have hHorizontal : referenceHighHorizontalAction g L q u y i = 0 := by
    simp only [referenceHighHorizontalAction,hDerivative,ContinuousLinearMap.zero_apply,
      hU,map_zero,zero_add]
  have hValue : referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i = 0 := by
    simp only [referenceHighFullAdjointFirstAction,hHorizontal,hU,map_zero,
      neg_zero,zero_add,smul_zero,sub_zero]
  change referenceHighFullAdjointFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i ≠ 0 at hy
  exact hy hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighFullAdjointFirstAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referenceHighFullAdjointFirstAction_subset
