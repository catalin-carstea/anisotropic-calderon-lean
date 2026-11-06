import Calderon.ActualConstantOneFirstSection
import Calderon.ActualConstantOneFirstSectionRegularity
import Calderon.ActualPhysicalHalfFirstSectionGraphDictionary
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceFiveHalfConstantFirstRegularPartInRoom
  referencePhysicalDensityHalfFromFirstSections referencePhysicalDensityOperator
  referenceHighDensityFirstAction sphereSobolevInclusionL sphereSobolevConstantOne constantOneFirstRaisingThreeHalf

def referenceConstantOneFirstSectionInRoom (q : ℝ) (R : R3 → ℝ) (i : Fin 3) (z : R3) : SphereSobolev (3/2:ℝ) :=
  (R z)⁻¹ • constantOneFirstRaisingThreeHalf hF i+
    referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(z,R z)),fderiv ℝ R z) i

def referenceConstantOnePhysicalDensityHalfInRoom (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (y : R3) : SphereSobolev (1/2:ℝ) :=
  referencePhysicalDensityHalfFromFirstSections
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
    (referenceConstantOneFirstSectionInRoom g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R) y

theorem sphereSobolevInclusionL_referenceConstantOnePhysicalDensityHalfInRoom
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3)
    (hRoom : ∀ᶠ z in 𝓝 y, ‖z-y0‖ ≤ ρ ∧ R z ≠ 0 ∧ (q,(z,R z)) ∈ K ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible ∧
      ∀ t ∈ uIcc (0:ℝ) (R z), (q,(z,t)) ∈
        referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceConstantOnePhysicalDensityHalfInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 g2 q R y) =
      referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y := by
  let eta := referenceConstantOneFirstSectionInRoom g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
  have hAt := hRoom.self_of_nhds
  have hEta (i : Fin 3) : ContDiffAt ℝ ∞ (eta i) y :=
    contDiffAt_constantOneFirstSection g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0
      hreg q R hR y i hAt.2.1 hAt.2.2.2.2
  have hEq (i : Fin 3) :
      (fun z => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (eta i z)) =ᶠ[𝓝 y]
      (fun z => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun _ => sphereSobolevConstantOne (3/2:ℝ)) z i) :=
    eventually_constantOneFirstSection_eq_original g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0
      hreg q hq R hR y i hRoom
  exact sphereSobolevInclusionL_referencePhysicalDensityHalfFromFirstSections
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R
    (fun _ => sphereSobolevConstantOne (3/2:ℝ)) eta y hEta hEq hInv hAt.2.2.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
