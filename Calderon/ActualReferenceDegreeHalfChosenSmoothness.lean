import Calderon.ActualReferenceDegreeHalfChosenSmoothnessCore
import Calderon.PhysicalDegreeCasimirExtractorSmoothNorm
import Calderon.ActualReferenceDegreeCommutatorHalfChosenDefinitions
import Calderon.ActualReferenceDegreeCasimirCompatibleData
import Calderon.PhysicalDegreeCasimirHalfExtractor
import Calderon.ClosedScalarCompatibilityQuotient
import Calderon.PhysicalDegreeCasimirSmoothRestriction
import Mathlib.Analysis.Calculus.ContDiff.Comp
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic PhysicalDegreeCasimirCompatibility ClosedScalarCompatibility
/-! Full upfront EXPANSION-v001.json. SAME original canonical named half family
norm infinity via original closed constraints and genuinely derived linear extractor. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referencePhysicalDegreeCasimirDataFamily
  referenceRadialDegreeCommutatorHighL

include hreg

lemma contDiffOn_referenceRadialDegreeCommutatorHalfFamily :
    ContDiffOn ℝ ∞ (referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hRestricted := contDiffOn_referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  have hExtract : ContDiff ℝ ∞ (compatibleDegreeHalfExtractorL hO hD :
      physicalDegreeCasimirCompatibleData hO hD →
        SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    contDiff_compatibleDegreeHalfExtractorL hO hD
  have hSmooth := ContDiff.comp_contDiffOn hExtract hRestricted
  exact hSmooth.congr (fun p hp => (compatibleDegreeHalfExtractorL_referenceData_eq g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp).symm)

lemma contDiffAt_referenceRadialDegreeCommutatorHalfFamily
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p :=
  (contDiffOn_referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0).contDiffAt
    ((isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)

lemma referenceRadialDegreeCommutatorHalfFamily_high_graph_on_locus
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (u : SphereSobolev (3/2:ℝ)) :
    referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) =
        referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u := by
  let x := referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p
  have hCoe : (x : PhysicalDegreeCasimirData) = referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p :=
    referenceDegreeCasimirCompatibleDataFamily_coe g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  have hRaw : compatibleDegreeRawHighL hO hD x = referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p :=
    (congrArg degreeRawHighDataL hCoe).trans (referencePhysicalDegreeCasimirDataFamily_raw_high g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p)
  calc
    _ = compatibleDegreeHalfExtractorL hO hD x
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) :=
      congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
        T (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))
          (compatibleDegreeHalfExtractorL_referenceData_eq g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp).symm
    _ = compatibleDegreeRawHighL hO hD x u := compatibleDegreeHalfExtractorL_high_graph hO hD x u
    _ = _ := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) hRaw

lemma norm_referenceRadialDegreeCommutatorHalfFamily_le_data_norm
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ‖referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ ≤
      12*Real.sqrt 2*‖referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p‖ := by
  let x := referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p
  have hCoe : (x : PhysicalDegreeCasimirData) = referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p :=
    referenceDegreeCasimirCompatibleDataFamily_coe g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  have hNorm : ‖x‖ = ‖referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p‖ :=
    norm_compatibleDegreeCasimirData_eq_of_coe_eq hO hD x _ hCoe
  have hBound := norm_compatibleDegreeHalfExtractorL_apply_le hO hD x
  have hValue := compatibleDegreeHalfExtractorL_referenceData_eq g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  calc
    _ = ‖compatibleDegreeHalfExtractorL hO hD x‖ := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => ‖T‖) hValue.symm
    _ ≤ 12*Real.sqrt 2*‖x‖ := hBound
    _ = _ := congrArg (fun t : ℝ => 12*Real.sqrt 2*t) hNorm

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRadialDegreeCommutatorHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRadialDegreeCommutatorHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfFamily_high_graph_on_locus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceRadialDegreeCommutatorHalfFamily_le_data_norm
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
