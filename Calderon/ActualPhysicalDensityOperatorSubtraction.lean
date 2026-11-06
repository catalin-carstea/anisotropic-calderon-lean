import Calderon.ActualDensityScalarCutoff
import Calderon.ActualPhysicalHalfFirstSectionGraphConvergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift ActualFiniteHarmonicCore

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceMetricGramFrame referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceHighAdjointMovingBoundaryActionFamily referenceLowerAdjointMovingBoundaryActionFamily
  referencePhysicalDensityOperator referenceDensityCovariantSecondAction sphereSobolevInclusionL
  referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

theorem referenceHighDensityFirstAction_sub
    (q : ℝ) (R : R3 → ℝ) (u v : R3 → SphereSobolev (3/2:ℝ))
    (y : R3) (i : Fin 3) (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (fun x => u x-v x) y i =
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i -
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i := by
  have hDerivative :
      fderiv ℝ (fun x => u x-v x) y (referenceMetricGramFrame g L (q,y) i) =
      fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i) -
        fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i) :=
    congrArg (fun A : R3 →L[ℝ] SphereSobolev (3/2:ℝ) => A (referenceMetricGramFrame g L (q,y) i))
      (fderiv_sub hu hv)
  simp only [referenceHighDensityFirstAction,referenceHighHorizontalAction]
  rw [hDerivative]
  simp only [map_sub]
  abel

theorem referenceLowerDensityFirstAction_sub
    (q : ℝ) (R : R3 → ℝ) (u v : R3 → SphereSobolev (1/2:ℝ))
    (y : R3) (i : Fin 3) (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (fun x => u x-v x) y i =
    referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i -
    referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i := by
  have hDerivative :
      fderiv ℝ (fun x => u x-v x) y (referenceMetricGramFrame g L (q,y) i) =
      fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i) -
        fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i) :=
    congrArg (fun A : R3 →L[ℝ] SphereSobolev (1/2:ℝ) => A (referenceMetricGramFrame g L (q,y) i))
      (fderiv_sub hu hv)
  simp only [referenceLowerDensityFirstAction,referenceLowerHorizontalAction]
  rw [hDerivative]
  simp only [map_sub]
  abel

private lemma referencePhysicalDensityOperator_eq_finiteContraction
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2:ℝ)) (y : R3) :
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    finiteSecondOrderContraction (R y)
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
      (fun i k j => referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j)
      (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,y))
      (fun i j => referenceLowerDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun z => referenceHighDensityFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u z j) y i)
      (fun k => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y k)) := by
  unfold referencePhysicalDensityOperator referenceDensityCovariantSecondAction finiteSecondOrderContraction
  rfl

theorem referencePhysicalDensityOperator_sub
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u v : R3 → SphereSobolev (3/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (y : R3) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
      g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R (fun x => u x-v x) y =
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y -
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y := by
  let A (i j : Fin 3) := referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let Gam (i k j : Fin 3) := referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j
  let b (i : Fin 3) := normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let X (t : R3 → SphereSobolev (3/2:ℝ)) (j : Fin 3) (z : R3) :=
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R t z j
  let O (t : R3 → SphereSobolev (3/2:ℝ)) (i j : Fin 3) := referenceLowerDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (X t j) y i
  let Z (t : R3 → SphereSobolev (3/2:ℝ)) (k : Fin 3) :=
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (X t k y)
  have hFirst (j : Fin 3) : X (fun z => u z-v z) j = fun z => X u j z-X v j z := by
    funext z
    exact referenceHighDensityFirstAction_sub
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u v z j
        (hu.differentiable (by simp) z) (hv.differentiable (by simp) z)
  have hUSmooth (j : Fin 3) : ContDiffAt ℝ ∞ (X u j) y := contDiffAt_referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y j hu.contDiffAt hR hr hInv hp
  have hVSmooth (j : Fin 3) : ContDiffAt ℝ ∞ (X v j) y := contDiffAt_referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R v y j hv.contDiffAt hR hr hInv hp
  have hOrdered (i j : Fin 3) : O (fun z => u z-v z) i j = O u i j-O v i j :=
    (congrArg (fun F : R3 → SphereSobolev (1/2:ℝ) => referenceLowerDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R F y i) (hFirst j)).trans
      (referenceLowerDensityFirstAction_sub
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (X u j) (X v j) y i
          ((hUSmooth j).differentiableAt (by simp)) ((hVSmooth j).differentiableAt (by simp)))
  have hZ (k : Fin 3) : Z (fun z => u z-v z) k = Z u k-Z v k := by
    have hPoint := congrFun (hFirst k) y
    exact (congrArg (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) hPoint).trans
      (map_sub _ _ _)
  have hOeq : O (fun z => u z-v z) = fun i j => O u i j-O v i j :=
    funext (fun i => funext (fun j => hOrdered i j))
  have hZeq : Z (fun z => u z-v z) = fun k => Z u k-Z v k := funext hZ
  have hChange := congrArg₂ (fun ox zz => finiteSecondOrderContraction (R y) A Gam b ox zz) hOeq hZeq
  have hLinear := finiteSecondOrderContraction_sub (R y) A Gam b (O u) (O v) (Z u) (Z v)
  have hFormula (t : R3 → SphereSobolev (3/2:ℝ)) := referencePhysicalDensityOperator_eq_finiteContraction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R t y
  exact (hFormula (fun z => u z-v z)).trans (hChange.trans (hLinear.trans
    (congrArg₂ (fun a b : SphereSobolev (-(1/2:ℝ)) => a-b) (hFormula u).symm (hFormula v).symm)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
