import Calderon.ActualReferenceSmoothMultiplierLowerCommutator
import Calderon.ActualReferenceLowerBoundaryTranspose
import Calderon.SphereSobolevPairingInclusion
import Calderon.SphereSobolevDualOrthogonalPullback
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open NativeCoefficientBoundaryMultiplier

local instance referenceSmoothCommutatorAdjointHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

lemma sphereSobolevDualPairing_realHalfOperatorAdjoint
    (G : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (u : SphereSobolev (1/2 : ℝ)) (z : SphereSobolev (-(1/2 : ℝ))) :
    sphereSobolevDualPairing (1/2 : ℝ) (G u) z =
      sphereSobolevDualPairing (1/2 : ℝ) u (realHalfOperatorAdjointL G z) := by
  change ⟪G u,z⟫_ℝ = ⟪u,ContinuousLinearMap.adjoint G z⟫_ℝ
  exact (ContinuousLinearMap.adjoint_inner_right G u z).symm

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
open Set

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceAdjointHalfRadial_smoothMultiplier_commutator_negative_factor
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u : SphereSobolev (1/2 : ℝ)) :
    let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let S := referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
    let M := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
    let Mn := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
    let G := referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p
    S (M u)-Mn (S u) = -(realHalfOperatorAdjointL G (J u)) := by
  intro J S M Mn G
  let A := referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hTranspose := sphereLowerDistributionalTranspose_referenceLowerRadial
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hp.2.1
  have hS (v z : SphereSobolev (1/2 : ℝ)) :
      sphereSobolevDualPairing (1/2 : ℝ) z (S v) =
        sphereSobolevDualPairing (1/2 : ℝ) v (A z) := by
    have hValue := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        sphereSobolevDualPairing (1/2 : ℝ) z (T v)) hTranspose
    exact hValue.symm.trans
      (sphereSobolevDualPairing_lower_distributionalTranspose A z v).symm
  have hM (v : SphereSobolev (1/2 : ℝ)) (z : SphereSobolev (-(1/2 : ℝ))) :
      sphereSobolevDualPairing (1/2 : ℝ) (M v) z =
        sphereSobolevDualPairing (1/2 : ℝ) v (Mn z) := by
    simpa only [M,Mn,nativeNegativeHalfCoefficientMulL] using
      sphereSobolevDualPairing_realHalfOperatorAdjoint M v z
  have hJ (v z : SphereSobolev (1/2 : ℝ)) :
      sphereSobolevDualPairing (1/2 : ℝ) v (J z) =
        sphereSobolevDualPairing (1/2 : ℝ) z (J v) := by
    have h1 := sphereSobolevDualPairing_inclusion_eq_inner_zero
      (1/2 : ℝ) (by norm_num) z v
    have h2 := sphereSobolevDualPairing_inclusion_eq_inner_zero
      (1/2 : ℝ) (by norm_num) v z
    change ⟪v,J z⟫_ℝ = ⟪z,J v⟫_ℝ
    exact (real_inner_comm _ _).trans
      (h1.trans ((real_inner_comm _ _).trans (h2.symm.trans (real_inner_comm _ _))))
  have hGraph (v : SphereSobolev (1/2 : ℝ)) : J (G v) = A (M v)-Mn (A v) :=
    referenceSmoothMultiplierBoundaryCommutatorFamily_lower_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q p hp v
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro v
  have hFirst : sphereSobolevDualPairing (1/2 : ℝ) v (S (M u)) =
      sphereSobolevDualPairing (1/2 : ℝ) u (Mn (A v)) :=
    (hS (M u) v).trans (hM u (A v))
  have hSecond : sphereSobolevDualPairing (1/2 : ℝ) v (Mn (S u)) =
      sphereSobolevDualPairing (1/2 : ℝ) u (A (M v)) :=
    (hM v (S u)).symm.trans (hS u (M v))
  calc
    _ = sphereSobolevDualPairing (1/2 : ℝ) v (S (M u))-
        sphereSobolevDualPairing (1/2 : ℝ) v (Mn (S u)) := by
      exact inner_sub_right _ _ _
    _ = sphereSobolevDualPairing (1/2 : ℝ) u (Mn (A v))-
        sphereSobolevDualPairing (1/2 : ℝ) u (A (M v)) :=
      congrArg₂ (fun a b : ℝ => a-b) hFirst hSecond
    _ = -(sphereSobolevDualPairing (1/2 : ℝ) u (A (M v)-Mn (A v))) := by
      simp only [sphereSobolevDualPairing,inner_sub_right]
      ring
    _ = -(sphereSobolevDualPairing (1/2 : ℝ) u (J (G v))) :=
      congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
        -(sphereSobolevDualPairing (1/2 : ℝ) u z)) (hGraph v).symm
    _ = -(sphereSobolevDualPairing (1/2 : ℝ) (G v) (J u)) := congrArg Neg.neg (hJ u (G v))
    _ = -(sphereSobolevDualPairing (1/2 : ℝ) v (realHalfOperatorAdjointL G (J u))) :=
      congrArg Neg.neg (sphereSobolevDualPairing_realHalfOperatorAdjoint G v (J u))
    _ = _ := by exact (inner_neg_right _ _).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_realHalfOperatorAdjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHalfRadial_smoothMultiplier_commutator_negative_factor
