import Calderon.ActualPhysicalNativeTraceFamilies
import Calderon.ActualHorizontalNativeTraceGraph
import Calderon.ActualNativeMovingRadiusTrace

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-PHYSICAL-HORIZONTAL-GRAPH-EXPANSION-v001.md. Same endpoint and native horizontal trace. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError NormalCoordinatesFrame
  SmoothMetricFrame MovingFrameConnection SmoothMovingFrameFields SmoothSphereFields
  NativeH2ThreeHalfValueTrace AmbientReferenceCovariantCore

theorem conformalReferenceGramFrameOperatorJoint_coordinate_eq_referenceFrame
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    conformalReferenceGramFrameOperatorJoint g L (q,y)
      (NormalCoordinatesFrame.coordinateVector i) = referenceMetricGramFrame g L (q,y) i := by
  calc
    _ = NormalCoordinatesFrame.frameOperator (conformalReferenceGramFrame g L (q,y))
        (NormalCoordinatesFrame.coordinateVector i) :=
      congrArg (fun A : R3 →L[ℝ] R3 => A (NormalCoordinatesFrame.coordinateVector i))
        (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))
    _ = conformalReferenceGramFrame g L (q,y) i :=
      frameOperator_coordinateVector _ i
    _ = _ := conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i

theorem conformalReferenceParallelAngularVelocity_eq_reference_neg_matrixVector
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (y X z : R3) :
    conformalReferenceParallelAngularVelocity g L q y X z =
    -matrixVector (referenceFrameConnectionCoefficient g L q y X) z := by
  ext a
  change conformalReferenceParallelAngularVelocity g L q y X z a =
    -(∑ b : Fin 3, referenceFrameConnectionCoefficient g L q y X a b * z b)
  have h := conformalReferenceParallelAngularVelocity_component g hg L q y X z a
  simpa only [NormalCoordinatesFrame.coordinateVector, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial,
    conformalReferenceFrameConnectionCoefficient_eq_referenceFrameConnectionCoefficient] using h

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referencePhysicalNativeThreeHalfTraceSection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (q : ℝ) (R : R3 → ℝ) (v : SmoothData)
    (y : R3) : SphereSobolev (3/2 : ℝ) :=
  nativeThreeHalfValueTraceL hcalc hF hO hD τ0
    (smoothBallSobolev 2
      (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v))

attribute [local irreducible] referenceMetricGramFrame referenceFrameConnectionCoefficient
  referencePhysicalMovingHorizontalSphere conformalReferenceGramFrameOperatorJoint
  conformalReferenceParallelAngularVelocity referencePhysicalNativeThreeHalfTraceSection

theorem ambientFrameHorizontal_referencePhysicalPullback_eq_physical
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : (y,0) ∈ B) (hr : R y ≠ 0) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (v : SmoothData) (x : UnitSphere) :
    ambientFrameHorizontal
      (fun z => referenceFrameConnectionCoefficient g L q z (referenceMetricGramFrame g L (q,z) i))
      (fun z => referenceMetricGramFrame g L (q,z) i)
      (fun p : R3 × R3 => v.1 (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2))))
      (y,x.val) =
    referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v x := by
  let G : R3 × R3 → ℝ := fun p =>
    v.1 (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2)))
  let e := referenceMetricGramFrame g L (q,y) i
  let F := conformalReferenceGramFrameOperatorJoint g L (q,y)
  have hFrame : F (NormalCoordinatesFrame.coordinateVector i) = e :=
    conformalReferenceGramFrameOperatorJoint_coordinate_eq_referenceFrame g L q y i
  have hDirection :
      (e,-matrixVector (referenceFrameConnectionCoefficient g L q y e) x.val) =
      (F (NormalCoordinatesFrame.coordinateVector i),
        conformalReferenceParallelAngularVelocity g L q y
          (F (NormalCoordinatesFrame.coordinateVector i)) x.val) := by
    apply Prod.ext
    · exact hFrame.symm
    · exact (conformalReferenceParallelAngularVelocity_eq_reference_neg_matrixVector
        g hg L q y e x.val).symm.trans
          (congrArg (fun X : R3 => conformalReferenceParallelAngularVelocity g L q y X x.val)
            hFrame.symm)
  have hSource := referencePhysicalMovingHorizontalSphere_source_derivative
    g hg L y0 Φ B ε C ρ H a w hData q hq R hR y hy hr i hInv v x
  dsimp only at hSource
  have hSourceTyped : fderiv ℝ G (y,x.val)
      (F (NormalCoordinatesFrame.coordinateVector i),
        conformalReferenceParallelAngularVelocity g L q y
          (F (NormalCoordinatesFrame.coordinateVector i)) x.val) =
      referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v x := by
    simpa only [G,F,conformalReferenceParallelAngularVelocity] using hSource
  exact (congrArg (fun V : R3 × R3 => fderiv ℝ G (y,x.val) V) hDirection).trans hSourceTyped

theorem referenceHighHorizontalAction_referencePhysicalNativeTrace_coarse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : (y,0) ∈ B) (hr : R y ≠ 0) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (v : SmoothData) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceHighHorizontalAction g L q
        (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 q R v) y i) =
    sphereSobolevZeroEquiv hO hD
      ((ContinuousMap.toLp 2 sphereProbability ℝ)
        (referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v)) := by
  let G : R3 × R3 → ℝ := fun p =>
    v.1 (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2)))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hG : ContDiff ℝ ∞ G := v.2.comp
    ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk (hR.comp contDiff_fst)).prodMk contDiff_snd)))
  let X : R3 → R3 := fun z => referenceMetricGramFrame g L (q,z) i
  have hX : ContDiff ℝ ∞ X := contDiff_referenceMetricGramFrame_slice g hg L q i
  let C0 : R3 → Fin 3 → Fin 3 → ℝ := fun z => referenceFrameConnectionCoefficient g L q z (X z)
  have hC : ∀ a b, ContDiff ℝ ∞ (fun z => C0 z a b) :=
    fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L q X hX a b
  let H0 := ambientFrameHorizontal C0 X G
  have hH : ContDiff ℝ ∞ H0 := contDiff_ambientFrameHorizontal C0 hC X hX G hG
  have hSection : nativeThreeHalfSmoothSection hcalc hF hO hD τ0 G hG =
      referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 q R v := by
    funext z
    unfold nativeThreeHalfSmoothSection referencePhysicalNativeThreeHalfTraceSection
    rfl
  have hAmbient : ambientSphereL2 H0 hH y =
      (ContinuousMap.toLp 2 sphereProbability ℝ)
        (referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v) := by
    apply congrArg (ContinuousMap.toLp 2 sphereProbability ℝ)
    apply ContinuousMap.ext
    intro x
    exact ambientFrameHorizontal_referencePhysicalPullback_eq_physical
      g hg L y0 Φ B ε C ρ H a w hData q hq R hR y hy hr i hInv v x
  have hGraph := referenceHighHorizontalAction_nativeThreeHalfSmoothSection_coarse
    g hg L q hcalc hF hO hD τ0 G hG y i
  have hSectionGraph := congrArg (fun U : R3 → SphereSobolev (3/2 : ℝ) =>
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceHighHorizontalAction g L q U y i)) hSection
  exact hSectionGraph.symm.trans
    (hGraph.trans (congrArg (sphereSobolevZeroEquiv hO hD) hAmbient))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.conformalReferenceGramFrameOperatorJoint_coordinate_eq_referenceFrame
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.conformalReferenceParallelAngularVelocity_eq_reference_neg_matrixVector
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalNativeThreeHalfTraceSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ambientFrameHorizontal_referencePhysicalPullback_eq_physical
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighHorizontalAction_referencePhysicalNativeTrace_coarse
