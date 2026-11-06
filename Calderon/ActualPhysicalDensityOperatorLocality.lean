import Calderon.ActualPhysicalDensityOperator

/-! Literal actual support locality; arbitrary intermediates. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointMovingBoundaryActionFamily
  referenceLowerAdjointMovingBoundaryActionFamily referenceHighHorizontalAngularL
  referenceLowerHorizontalAngularL sphereSobolevInclusionL referenceMetricGramFrame
  referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceDensityCovariantSecondAction referencePhysicalDensityOperator

theorem tsupport_referenceHighDensityFirstAction_subset
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (i : Fin 3) :
    tsupport (fun y => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) ⊆ tsupport u := by
  classical
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hValue : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hOutside
  apply hy
  simp only [referenceHighDensityFirstAction, referenceHighHorizontalAction,
    hValue, hDerivative, ContinuousLinearMap.zero_apply, map_zero, add_zero]

theorem tsupport_referenceLowerDensityFirstAction_subset
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (1/2 : ℝ)) (i : Fin 3) :
    tsupport (fun y => referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) ⊆ tsupport u := by
  classical
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hValue : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hOutside
  apply hy
  simp only [referenceLowerDensityFirstAction, referenceLowerHorizontalAction,
    hValue, hDerivative, ContinuousLinearMap.zero_apply, map_zero, add_zero]

theorem tsupport_referencePhysicalDensityOperator_subset
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) :
    tsupport (fun y => referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y) ⊆ tsupport u := by
  classical
  have hFirst (j : Fin 3) : tsupport (fun x => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) ⊆ tsupport u :=
    tsupport_referenceHighDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u j
  have hOrdered (i j : Fin 3) : tsupport (fun y => referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) y i) ⊆ tsupport u :=
    (tsupport_referenceLowerDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) i).trans (hFirst j)
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hFirstZero (j : Fin 3) : referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y j = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun x : R3 => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) (x := y)
      (fun h => hOutside (hFirst j h))
  have hOrderedZero (i j : Fin 3) : referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) y i = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun z : R3 => referenceLowerDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun x => referenceHighDensityFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) z i) (x := y)
      (fun h => hOutside (hOrdered i j h))
  apply hy
  simp only [referencePhysicalDensityOperator, referenceDensityCovariantSecondAction,
    hFirstZero, hOrderedZero, map_zero, smul_zero, Finset.sum_const_zero, sub_zero, add_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referenceHighDensityFirstAction_subset
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referenceLowerDensityFirstAction_subset
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referencePhysicalDensityOperator_subset
