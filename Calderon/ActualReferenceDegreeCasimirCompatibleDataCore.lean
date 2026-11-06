import Calderon.PhysicalDegreeCasimirCompatibilitySpace
import Calderon.ActualReferenceMidpointFinitePhysicalCasimir
import Calderon.ActualReferenceAdjointAngleDerivativePhysicalPairing
import Calderon.ActualReferenceDegreeCommutatorHighBlock
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic PhysicalDegreeCasimirCompatibility
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referencePhysicalDegreeCasimirDataFamily (p : ℝ × (R3 × ℝ)) : PhysicalDegreeCasimirData :=
  (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p,
    ((fun ij : Fin 3 × Fin 3 => referenceRadialRotationCommutatorMidpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p),
      (fun ij : Fin 3 × Fin 3 => referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 p)))

attribute [local irreducible] referenceRadialRotationCommutatorMidpointFamily
  referenceAdjointMidpointAngleDerivativeFamily referenceLowerRadialEndpointFamily
  referenceSharpRadialTraceFamily sphereSobolevSingleL sphereSobolevCoefficientL
  sphereSobolevZeroEquiv sphereSobolevInclusionL

lemma referencePhysicalDegreeCasimirDataFamily_endpoint_scalar
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (m : ℕ) (u : SphereSobolev (3/2:ℝ)) (v : harmonicSphereSubspace m) :
    degreeEndpointScalarL m u v (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p) = 0 := by
  have hDefect := (sphereSobolevEndpointDefectL_eq_zero_iff
    (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)).2
      (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)
  rw [degreeEndpointScalarL_apply]
  change ⟪sphereSobolevCoefficientL (-1/2:ℝ) m
    (sphereSobolevEndpointDefectL (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) u),v⟫_ℝ = 0
  rw [hDefect]
  simp only [ContinuousLinearMap.zero_apply,map_zero,inner_zero_left]

lemma referencePhysicalDegreeCasimirDataFamily_casimir_scalar
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (ncut mcut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    degreeFiniteCasimirScalarL hO hD ncut mcut u v
      (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p) = 0 := by
  have hOriginal := referenceRadialRotationCommutatorMidpoint_finite_physical_casimir_form
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp (Finset.range ncut) (Finset.range mcut) u v
  have hValue := degreeFiniteCasimirScalarL_apply hO hD ncut mcut u v
    (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p)
  apply hValue.trans
  apply sub_eq_zero.mpr
  simpa only [referencePhysicalDegreeCasimirDataFamily,referenceRadialEndpointPairFamily,
    referenceSharpRadialHarmonicBlockL,ContinuousLinearMap.comp_apply,
    Fintype.sum_prod_type] using hOriginal

lemma referencePhysicalDegreeCasimirDataFamily_adjoint_scalar
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (ij : Fin 3 × Fin 3) (f v : SphereSobolev 1) :
    degreeAdjointScalarL hO hD ij f v
      (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p) = 0 := by
  have hValue := degreeAdjointScalarL_apply hO hD ij f v
    (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p)
  apply hValue.trans
  apply sub_eq_zero.mpr
  exact inner_probability_referenceCmid_adjointMidpointAngleDerivative
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 p hp f v

lemma referencePhysicalDegreeCasimirDataFamily_mem
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p ∈ physicalDegreeCasimirCompatibleData hO hD := by
  apply (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).2
  intro z
  rcases z with z | z
  · exact referencePhysicalDegreeCasimirDataFamily_endpoint_scalar g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp z.1 z.2.1 z.2.2
  · rcases z with z | z
    · exact referencePhysicalDegreeCasimirDataFamily_casimir_scalar g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp z.1.1 z.1.2 z.2.1 z.2.2
    · exact referencePhysicalDegreeCasimirDataFamily_adjoint_scalar g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp z.1 z.2.1 z.2.2

lemma contDiffAt_referencePhysicalDegreeCasimirDataFamily
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0) p := by
  have hLower := contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.2.2 hp.2.1
  have hSharp := contDiffAt_referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.1
  have hEndpoints : ContDiffAt ℝ ∞ (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p :=
    hLower.prodMk hSharp
  have hP : ContDiffAt ℝ ∞
      (fun t : ℝ × (R3 × ℝ) => fun ij : Fin 3 × Fin 3 =>
        referenceRadialRotationCommutatorMidpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 t) p :=
    contDiffAt_pi.2 (fun ij => contDiffAt_referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p hp)
  have hQ : ContDiffAt ℝ ∞
      (fun t : ℝ × (R3 × ℝ) => fun ij : Fin 3 × Fin 3 =>
        referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 t) p :=
    contDiffAt_pi.2 (fun ij => contDiffAt_referenceAdjointMidpointAngleDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 p hp)
  exact hEndpoints.prodMk (hP.prodMk hQ)

lemma contDiffOn_referencePhysicalDegreeCasimirDataFamily :
    ContDiffOn ℝ ∞ (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro p hp
  exact (contDiffAt_referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp).contDiffWithinAt

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDegreeCasimirDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDegreeCasimirDataFamily_endpoint_scalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDegreeCasimirDataFamily_casimir_scalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDegreeCasimirDataFamily_adjoint_scalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDegreeCasimirDataFamily_mem
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referencePhysicalDegreeCasimirDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referencePhysicalDegreeCasimirDataFamily
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
