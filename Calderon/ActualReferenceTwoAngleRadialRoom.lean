import Calderon.ActualReferenceTwoAngleStrongOriginalRoom
import Calderon.ActualReferenceRadialEndpointOpenLocus

/-! Actual common open inverse room. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open Filter
open scoped Topology

open SphereHarmonic

def referenceTwoAngleRadialInvertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    Set (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :=
  (Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) ∩
  {t | (referenceTwoAngleStrongDirichletFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible}

lemma isOpen_referenceTwoAngleRadialInvertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    IsOpen (referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :=
  (isOpen_univ.prod (isOpen_univ.prod
    (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0))).inter
    (isOpen_referenceTwoAngleStrong_inverse_set g L y0 Φ B ε C ρ H a w hData hcalc i j k l)

lemma referenceTwoAngleRadialInvertibleLocus_zero_angles
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (0,(0,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l := by
  refine ⟨⟨Set.mem_univ _,Set.mem_univ _,hp⟩,?_⟩
  change (referenceTwoAngleStrongDirichletFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(0,p))).IsInvertible
  rw [referenceTwoAngleStrongDirichletFamily_zero_angles]
  exact hp.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleRadialInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceTwoAngleRadialInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleRadialInvertibleLocus_zero_angles
