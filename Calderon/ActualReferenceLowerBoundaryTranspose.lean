import Calderon.ActualReferenceAdjointHalfRadialDuality
import Calderon.SphereSobolevPairing
import Calderon.SphereSobolevCompletion
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

local instance : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

/-! Upfront: day-oct13/actual-boundary-moving-operator-oct15-v001/
EXPANSION-lower-boundary-action.md. The following equivalence changes the
interpretation of the raw carrier; it is NOT physical Sobolev inclusion. -/

def sphereHalfDualCarrierEquiv :
    SphereSobolev (1/2 : ℝ) ≃ₗᵢ[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  LinearIsometryEquiv.refl ℝ (SphereSobolev (1/2 : ℝ))

theorem sphereSobolevCoefficientL_halfDualCarrier (u : SphereSobolev (1/2 : ℝ))
    (k : ℕ) :
    sphereSobolevCoefficientL (-(1/2 : ℝ)) k (sphereHalfDualCarrierEquiv u) =
      besselWeight (1/2 : ℝ) k • u k := by
  simp only [sphereSobolevCoefficientL,neg_neg]
  rfl

theorem sphereSobolevCoefficientL_halfDualCarrier_symm
    (v : SphereSobolev (-(1/2 : ℝ))) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (sphereHalfDualCarrierEquiv.symm v) =
      besselWeight (-(1/2 : ℝ)) k • v k := rfl

theorem besselWeight_half_dual_mul (k : ℕ) :
    besselWeight (-(1/2 : ℝ)) k * besselWeight (1/2 : ℝ) k = 1 := by
  simpa only [besselWeight,neg_add_cancel,Real.rpow_zero] using
    (Real.rpow_add (by positivity : 0 < 1 + (k : ℝ)) (-(1/2 : ℝ)) (1/2 : ℝ)).symm

theorem sphereSobolevDualPairing_half_eq_weighted_carrier_sum
    (u : SphereSobolev (1/2 : ℝ)) (v : SphereSobolev (-(1/2 : ℝ))) :
    sphereSobolevDualPairing (1/2 : ℝ) u v =
      ∑' k : ℕ, ⟪besselWeight (-(1/2 : ℝ)) k • u k,
        besselWeight (1/2 : ℝ) k • v k⟫_ℝ := by
  rw [sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  simp only [sphereSobolevCoefficientL,neg_neg,ContinuousLinearMap.smul_apply]
  rfl

def sphereLowerDistributionalTranspose
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  sphereHalfDualCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.adjoint A).comp
      sphereHalfDualCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap)

theorem sphereSobolevDualPairing_lower_distributionalTranspose
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v (A u) =
      sphereSobolevDualPairing (1/2 : ℝ) u (sphereLowerDistributionalTranspose A v) := by
  change ⟪v,A u⟫_ℝ = ⟪u,ContinuousLinearMap.adjoint A v⟫_ℝ
  exact (real_inner_comm (A u) v).trans
    (ContinuousLinearMap.adjoint_inner_right A u v).symm

end OAI.AnisotropicCalderon.SphereHarmonic

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem sphereLowerDistributionalTranspose_referenceLowerRadial
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    sphereLowerDistributionalTranspose
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  change sphereSobolevDualPairing (1/2 : ℝ) u
    (sphereLowerDistributionalTranspose
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) v) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v)
  rw [← sphereSobolevDualPairing_lower_distributionalTranspose]
  exact sphereSobolevDualPairing_referenceLowerRadial_adjoint
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hOriginal u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereHalfDualCarrierEquiv
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_halfDualCarrier
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_halfDualCarrier_symm
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.besselWeight_half_dual_mul
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_half_eq_weighted_carrier_sum
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_lower_distributionalTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereLowerDistributionalTranspose_referenceLowerRadial
