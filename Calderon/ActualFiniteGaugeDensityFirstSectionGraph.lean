import Calderon.ActualFiniteGaugeDensityFirstSection
import Calderon.ActualFiniteGaugeAdjointMovingBoundaryGraph

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
DIRECT-FINITE-PHYSICAL-DENSITY-DOMAIN-EXPANSION-v001.md. Literal eta, actual uncompressed first outputs. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection
  referenceFiniteHighHorizontalSection referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAction sphereSobolevInclusionL sphereSobolevPartialSumL nativeThreeHalfCoefficientMulL
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

lemma eventually_sphereSobolevInclusionL_referenceFiniteGaugeDensityFirstSection
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (n : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (hu : ContDiff ℝ ∞ u) (y : R3)
    (hpK : (q,(y,R y)) ∈ KJ) (lam Lam : ℝ)
    (hNear : ∀ᶠ z in 𝓝 y, ‖z-y0‖ ≤ ρ ∧
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a ((q,(z,R z)),x)) lam Lam ∧
      (∀ x ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(z,R z)),x)‖ ≤ lam/4) ∧
      (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      (q,(z,R z)) ∈ G.parameterRoom) (i : Fin 3) :
    (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteGaugeDensityFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u x i)) =ᶠ[𝓝 y]
    (fun x => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) x i) := by
  let T : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,R x))
  have hT : Continuous T := continuous_const.prodMk (continuous_id.prodMk hR.continuous)
  have hCoefficients : ∀ᶠ t in 𝓝 (T y), ∀ j : Fin 3,
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (E.jets i j t) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j t) := by
    apply Filter.eventually_all.mpr
    intro j
    exact E.eventually_nativeThreeHalfCoefficientMulL_jets_eq hcalc hF hO hD τ0 (T y) hpK i j
  have hNearCoeff := hT.continuousAt.eventually hCoefficients
  filter_upwards [hNear,hNearCoeff] with z hz hCoeff
  have hHorizontal := sphereSobolevInclusionL_referenceFiniteHighHorizontalSection
    g L hcalc hF hO hD τ0 n q u z i (hu.contDiffAt.differentiableAt (by simp))
  have hMoving := sphereSobolevInclusionL_referenceFiniteGaugeAdjointMovingBoundaryFamily_of_coefficient_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E hreg hKernel n q hq R z
      hz.1 lam Lam hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2 i hCoeff (u z)
  have hMoving' : sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteGaugeAdjointMovingBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R z i (u z)) =
      referenceHighAdjointMovingBoundaryActionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,z) i
          (sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) :=
    hMoving.trans (congrArg
      (referenceHighAdjointMovingBoundaryActionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,z) i)
      (sphereSobolevPartialSumL_apply (3/2 : ℝ) n (u z)).symm)
  have hCombined := congrArg₂ (fun v w : SphereSobolev (1/2 : ℝ) => v+w) hHorizontal hMoving'
  simpa only [referenceFiniteGaugeDensityFirstSection,referenceHighDensityFirstAction,map_add] using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_sphereSobolevInclusionL_referenceFiniteGaugeDensityFirstSection
