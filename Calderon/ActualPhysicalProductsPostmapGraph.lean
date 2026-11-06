import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore
import Calderon.SphereSobolevInclusion

/-! Complete AUTHOR beforecode proposal only. No executable or acceptance grant.
Canonical Half postmap and exact original pointwise Products room conditions. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
open Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds

theorem physicalProductsPostmap_negative_graph_of_radial_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (hr : R y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let K : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let Iin : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Fh := fun (i : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Fl := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
    let Eh := fun (i : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
    let El := fun i : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
    let F := fun (i : Fin 3) (x : R3) => Iin (Fh i x (u x))
    let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
    let MF := fun i : Fin 3 => Iout.comp (Fl i)
    let ME := El
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let r := R y
    let UFE := fun i j : Fin 3 => MF i (E j y)+ME i (F j y)
    let UProducts := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UFE i j)
    K ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 q R y (u y)))) = UProducts := by
  classical
  intro K0 dIin dIout dFh dFl dEh dEl dF dE dMF dME dQ drad dUFE dUProducts
  let v : SphereSobolev (1/2 : ℝ) :=
    referencePhysicalDensityProductsHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y)
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    ((sphereSobolevZeroEquiv hO hD).apply_symm_apply
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v))
  have hTrans := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v)
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  have hPostmap : K0 ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v)) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v :=
    hCancel.trans hTrans
  have hNegative := referencePhysicalDensityProductsHalfOperator_negative_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 q hq R hR y
    hy hr hInv hSegment (u y)
  have hGraph := hPostmap.trans hNegative
  have hProductsValue :
      (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
          (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
            (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
              ((q,y),fderiv ℝ R y) i
              (referenceHighAdjointMovingDifferenceQuotient
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j (u y))) +
           referenceLowerAdjointMovingDifferenceQuotient
             g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
             (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
               (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
                 ((q,y),fderiv ℝ R y) j (u y))))) = dUProducts := by
    dsimp only [dUProducts,drad,dQ,dUFE,dMF,dFl,dE,dEh,dME,dEl,
      dF,dIin,dFh,dIout] <;> rfl
  have hResult := hGraph.trans hProductsValue
  exact hResult

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
