import Calderon.ActualReferenceTwoAngleDegreeFiniteCasimir
import Calderon.ActualReferenceTwoAngleFirstAdjointMidpointDerivative
import Calderon.PhysicalDegreeCasimirCompatibilitySpace

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-actual-closed-degree-data-v119.md. Actual data, no desired gain premise. -/
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
  (k l : Fin 3)

def referenceTwoAnglePhysicalDegreeCasimirDataFamily
    (z : ℝ × (ℝ × (R3 × ℝ))) : PhysicalDegreeCasimirData :=
  (referenceTwoAngleRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z),
    ((fun ij : Fin 3 × Fin 3 => referenceTwoAngleFirstMidpointDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 k l z),
      (fun ij : Fin 3 × Fin 3 => referenceTwoAngleFirstAdjointMidpointDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 ij.1 ij.2 k l z)))

attribute [local irreducible] referenceTwoAngleFirstMidpointDerivativeFamily
  referenceTwoAngleFirstAdjointMidpointDerivativeFamily referenceTwoAngleLowerRadialEndpointFamily
  referenceTwoAngleSharpRadialTraceFamily referenceRotationSharpRadialTraceFamily
  sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevZeroEquiv sphereSobolevInclusionL

lemma referenceTwoAnglePhysicalDegreeCasimirDataFamily_endpoint_scalar
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : ∀ i j : Fin 3, (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (m : ℕ) (u : SphereSobolev (3/2:ℝ)) (v : harmonicSphereSubspace m) :
    degreeEndpointScalarL m u v (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p)) = 0 := by
  have hDefect := (sphereSobolevEndpointDefectL_eq_zero_iff
    (referenceTwoAngleRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p)))).2
      (referenceTwoAngleRadialEndpointPairFamily_mem_compatible
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p)) (hp 0 0))
  rw [degreeEndpointScalarL_apply]
  change ⟪sphereSobolevCoefficientL (-1/2:ℝ) m
    (sphereSobolevEndpointDefectL (referenceTwoAngleRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p))) u),v⟫_ℝ = 0
  rw [hDefect]
  simp only [ContinuousLinearMap.zero_apply,map_zero,inner_zero_left]

lemma referenceTwoAnglePhysicalDegreeCasimirDataFamily_casimir_scalar
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : ∀ i j : Fin 3, (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (ncut mcut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    degreeFiniteCasimirScalarL hO hD ncut mcut u v
      (referenceTwoAnglePhysicalDegreeCasimirDataFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p)) = 0 := by
  have hOriginal := referenceTwoAngleFirstMidpoint_finite_physical_casimir_form
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p hp
      (Finset.range ncut) (Finset.range mcut) u v
  have hZero := referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l φ p
  have hValue := degreeFiniteCasimirScalarL_apply hO hD ncut mcut u v
    (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p))
  apply hValue.trans
  apply sub_eq_zero.mpr
  simpa only [referenceTwoAnglePhysicalDegreeCasimirDataFamily,
    referenceTwoAngleRadialEndpointPairFamily,referenceTwoAngleBackgroundSharpHarmonicBlockL,
    ContinuousLinearMap.comp_apply,Fintype.sum_prod_type,hZero] using hOriginal

lemma referenceTwoAnglePhysicalDegreeCasimirDataFamily_adjoint_scalar
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : ∀ i j : Fin 3, (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (ij : Fin 3 × Fin 3) (f v : SphereSobolev 1) :
    degreeAdjointScalarL hO hD ij f v
      (referenceTwoAnglePhysicalDegreeCasimirDataFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p)) = 0 := by
  have hValue := degreeAdjointScalarL_apply hO hD ij f v
    (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p))
  apply hValue.trans
  apply sub_eq_zero.mpr
  exact inner_probability_referenceTwoAngleFirstMidpointDerivative_adjoint
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
      ij.1 ij.2 k l φ p (hp ij.1 ij.2) f v

lemma referenceTwoAnglePhysicalDegreeCasimirDataFamily_mem
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : ∀ i j : Fin 3, (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p) ∈
        physicalDegreeCasimirCompatibleData hO hD := by
  apply (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).2
  intro z
  rcases z with z | z
  · exact referenceTwoAnglePhysicalDegreeCasimirDataFamily_endpoint_scalar
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l φ p hp z.1 z.2.1 z.2.2
  · rcases z with z | z
    · exact referenceTwoAnglePhysicalDegreeCasimirDataFamily_casimir_scalar
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l φ p hp z.1.1 z.1.2 z.2.1 z.2.2
    · exact referenceTwoAnglePhysicalDegreeCasimirDataFamily_adjoint_scalar
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l φ p hp z.1 z.2.1 z.2.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePhysicalDegreeCasimirDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePhysicalDegreeCasimirDataFamily_endpoint_scalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePhysicalDegreeCasimirDataFamily_casimir_scalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePhysicalDegreeCasimirDataFamily_adjoint_scalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePhysicalDegreeCasimirDataFamily_mem
