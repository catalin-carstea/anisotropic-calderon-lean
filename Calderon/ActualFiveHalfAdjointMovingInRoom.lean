import Calderon.ActualFiveHalfAdjointJacobiInRoom
import Calderon.ActualHighAdjointMovingBoundaryFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
attribute [local irreducible] referenceRadialEndpointInvertibleLocus referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceHighAdjointCoordinateBoundaryFamily
  ReferenceJacobiCompactExtensionRoom.fiveHalfMultiplierFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
private def threeScalarCombination {F : Type*} [AddCommGroup F] [Module ℝ F]
    (r s c : ℝ) (Q J A : F) : F := r • Q + s • J + c • A

private lemma contDiffAt_threeScalarCombination
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r s c : ℝ × R3 → ℝ) (Q J A : ℝ × R3 → F) (t : ℝ × R3)
    (hr : ContDiffAt ℝ ∞ r t) (hs : ContDiffAt ℝ ∞ s t)
    (hc : ContDiffAt ℝ ∞ c t) (hQ : ContDiffAt ℝ ∞ Q t)
    (hJ : ContDiffAt ℝ ∞ J t) (hA : ContDiffAt ℝ ∞ A t) :
    ContDiffAt ℝ ∞ (fun x => threeScalarCombination (r x) (s x) (c x) (Q x) (J x) (A x)) t := by
  exact ((hr.smul hQ).add (hs.smul hJ)).add (hc.smul hA)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)

attribute [local irreducible] referenceFiveHalfAdjointJacobiBoundaryInRoom

def referenceFiveHalfAdjointMovingBoundaryInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  threeScalarCombination (F := SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    ((R t.2)⁻¹) (R t.2) (referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i)
    (referenceFiveHalfAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i)
    (referenceFiveHalfAdjointJacobiBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i)
    (referenceAdjointFiveHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2)))

private lemma moving_coordinate_composition
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hp : (t.1,(t.2,R t.2)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun s : ℝ × R3 => referenceFiveHalfAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s.1,(s.2,R s.2)) i) t := by
  have hT : ContDiffAt ℝ ∞ (fun s : ℝ × R3 => (s.1,(s.2,R s.2))) t :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hR.comp t contDiffAt_snd))
  exact (contDiffAt_referenceFiveHalfAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (t.1,(t.2,R t.2)) i hp).comp t hT

private lemma moving_jacobi_composition
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hp : (t.1,(t.2,R t.2)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun s : ℝ × R3 => referenceFiveHalfAdjointJacobiBoundaryInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 (s.1,(s.2,R s.2)) i) t := by
  have hT : ContDiffAt ℝ ∞ (fun s : ℝ × R3 => (s.1,(s.2,R s.2))) t :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hR.comp t contDiffAt_snd))
  exact (contDiffAt_referenceFiveHalfAdjointJacobiBoundaryInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg (t.1,(t.2,R t.2)) i hp).comp t hT

private lemma moving_radial_composition
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hp : (t.1,(t.2,R t.2)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun s : ℝ × R3 => referenceAdjointFiveHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s.1,(s.2,R s.2))) t := by
  have hT : ContDiffAt ℝ ∞ (fun s : ℝ × R3 => (s.1,(s.2,R s.2))) t :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hR.comp t contDiffAt_snd))
  exact ((contDiffOn_referenceAdjointFiveHalfRadialFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)).comp t hT

lemma contDiffAt_referenceFiveHalfAdjointMovingBoundaryInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hp : (t.1,(t.2,R t.2)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun s => referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R s i) t    := by
  have hRadius : ContDiffAt ℝ ∞ (fun x : ℝ × R3 => R x.2) t := hR.comp t contDiffAt_snd
  have hQ := moving_coordinate_composition g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 hreg R t i hR hr hp
  have hJ := moving_jacobi_composition g L y0 Φ B ε C ρ H a w hData hg E
    hcalc hF hO hD τ0 hreg R t i hR hr hp
  have hA := moving_radial_composition g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 hreg R t i hR hr hp
  have hc : ContDiffAt ℝ ∞ (fun x : ℝ × R3 => referenceRadiusHorizontalLogDerivative g L x.1 R x.2 i) t :=
    contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R t i hR hr
  exact contDiffAt_threeScalarCombination
    (F := SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (fun x => (R x.2)⁻¹) (fun x => R x.2)
    (fun x => referenceRadiusHorizontalLogDerivative g L x.1 R x.2 i)
    (fun x => referenceFiveHalfAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (x.1,(x.2,R x.2)) i)
    (fun x => referenceFiveHalfAdjointJacobiBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 (x.1,(x.2,R x.2)) i)
    (fun x => referenceAdjointFiveHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (x.1,(x.2,R x.2))) t
    (hRadius.inv hr) hRadius hc hQ hJ hA

lemma referenceFiveHalfAdjointMovingBoundaryInRoom_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3) (u : SphereSobolev (5/2:ℝ)) :
    referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R t i u =
    (R t.2)⁻¹ • (referenceFiveHalfAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i u) +
    R t.2 • (referenceFiveHalfAdjointJacobiBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i u) +
    referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i •
      (referenceAdjointFiveHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) u) := by
  simp only [referenceFiveHalfAdjointMovingBoundaryInRoom,threeScalarCombination,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
