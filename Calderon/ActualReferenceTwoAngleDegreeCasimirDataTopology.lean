import Calderon.ActualReferenceTwoAngleDegreeCasimirData
import Calderon.ActualReferenceTwoAngleLowerRadialEndpoint
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual finite inverse intersection. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic PhysicalDegreeCasimirCompatibility
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (k l : Fin 3)

def referenceTwoAngleDegreeDataInvertibleLocus : Set (ℝ × (ℝ × (R3 × ℝ))) :=
  ⋂ ij : Fin 3 × Fin 3, (fun z : ℝ × (ℝ × (R3 × ℝ)) => (0,z)) ⁻¹'
    referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 k l

attribute [local irreducible] referenceTwoAnglePhysicalDegreeCasimirDataFamily
  referenceTwoAngleLowerRadialEndpointFamily referenceTwoAngleSharpRadialTraceFamily
  referenceTwoAngleFirstMidpointDerivativeFamily referenceTwoAngleFirstAdjointMidpointDerivativeFamily

lemma isOpen_referenceTwoAngleDegreeDataInvertibleLocus :
    IsOpen (referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) := by
  apply isOpen_iInter_of_finite
  intro ij
  exact (isOpen_referenceTwoAngleRadialInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 k l).preimage
      (continuous_const.prodMk continuous_id)

lemma referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (0,p) ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l := by
  apply Set.mem_iInter.mpr
  intro ij
  exact referenceTwoAngleRadialInvertibleLocus_zero_angles
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 k l p hp

lemma contDiffAt_referenceTwoAnglePhysicalDegreeCasimirDataFamily
    (hreg : FixedDirichletRegularity) (z : ℝ × (ℝ × (R3 × ℝ)))
    (hz : z ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) :
    ContDiffAt ℝ ∞ (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l) z := by
  have hij (i j : Fin 3) : (0,z) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l :=
    Set.mem_iInter.mp hz (i,j)
  have hOrig := (hij 0 0).1.2.2
  have hInsert : ContDiffAt ℝ ∞
      (fun t : ℝ × (ℝ × (R3 × ℝ)) => ((0:ℝ),t)) z :=
    contDiffAt_const.prodMk contDiffAt_id
  have hPair : ContDiffAt ℝ ∞
      (fun t : ℝ × (ℝ × (R3 × ℝ)) => referenceTwoAngleRadialEndpointPairFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,t)) z :=
    ((contDiffAt_referenceTwoAngleLowerRadialEndpointFamily_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z) hOrig.2.2 hOrig.2.1).prodMk
      (contDiffAt_referenceTwoAngleSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z) (hij 0 0).2)).comp z hInsert
  have hPrimal : ContDiffAt ℝ ∞
      (fun t : ℝ × (ℝ × (R3 × ℝ)) => fun ij : Fin 3 × Fin 3 =>
        referenceTwoAngleFirstMidpointDerivativeFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 k l t) z :=
    contDiffAt_pi.2 (fun ij => contDiffAt_referenceTwoAngleFirstMidpointDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 k l z (hij ij.1 ij.2))
  have hAdjoint : ContDiffAt ℝ ∞
      (fun t : ℝ × (ℝ × (R3 × ℝ)) => fun ij : Fin 3 × Fin 3 =>
        referenceTwoAngleFirstAdjointMidpointDerivativeFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 k l t) z :=
    contDiffAt_pi.2 (fun ij => contDiffAt_referenceTwoAngleFirstAdjointMidpointDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 k l z (hij ij.1 ij.2))
  unfold referenceTwoAnglePhysicalDegreeCasimirDataFamily
  exact hPair.prodMk (hPrimal.prodMk hAdjoint)

lemma contDiffOn_referenceTwoAnglePhysicalDegreeCasimirDataFamily
    (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞ (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l)
      (referenceTwoAngleDegreeDataInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) := by
  intro z hz
  exact (contDiffAt_referenceTwoAnglePhysicalDegreeCasimirDataFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l hreg z hz).contDiffWithinAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeDataInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceTwoAngleDegreeDataInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAnglePhysicalDegreeCasimirDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAnglePhysicalDegreeCasimirDataFamily
