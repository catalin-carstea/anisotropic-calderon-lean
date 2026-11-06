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

def referenceDegreeCasimirCompatibleDataFamily :
    (ℝ × (R3 × ℝ)) → physicalDegreeCasimirCompatibleData hO hD :=
  physicalDegreeCasimirRestriction hO hD
    (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
    (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (fun p hp => (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).1
      (referencePhysicalDegreeCasimirDataFamily_mem g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp))

attribute [local irreducible] referencePhysicalDegreeCasimirDataFamily
  referenceRadialDegreeCommutatorHighL

lemma referenceDegreeCasimirCompatibleDataFamily_coe
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p : PhysicalDegreeCasimirData) =
      referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p :=
  physicalDegreeCasimirRestriction_coe_of_mem hO hD
    (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
    (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (fun z hz => (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).1
      (referencePhysicalDegreeCasimirDataFamily_mem g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 z hz)) p hp

lemma contDiffOn_referenceDegreeCasimirCompatibleDataFamily :
    ContDiffOn ℝ ∞ (referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiffOn_physicalDegreeCasimirRestriction hO hD
    (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
    (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (fun p hp => (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).1
      (referencePhysicalDegreeCasimirDataFamily_mem g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp))
    (contDiffOn_referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)

lemma compatibleDegreeHalfExtractorL_referenceData_eq
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    compatibleDegreeHalfExtractorL hO hD (referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p) =
      referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
  let x := referenceDegreeCasimirCompatibleDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p
  have hCoe : (x : PhysicalDegreeCasimirData) = referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p :=
    referenceDegreeCasimirCompatibleDataFamily_coe g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  have hRaw : compatibleDegreeRawHighL hO hD x = referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p :=
    (congrArg degreeRawHighDataL hCoe).trans (referencePhysicalDegreeCasimirDataFamily_raw_high g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p)
  rw [compatibleDegreeHalfExtractorL_apply]
  exact congrArg
    (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T.toLinearMap.extendOfNorm (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap) hRaw

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDegreeCasimirCompatibleDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDegreeCasimirCompatibleDataFamily_coe
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceDegreeCasimirCompatibleDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.compatibleDegreeHalfExtractorL_referenceData_eq
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
