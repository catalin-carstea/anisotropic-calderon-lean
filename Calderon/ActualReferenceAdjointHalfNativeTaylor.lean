import Calderon.ActualReferenceHighAdjointRadialNativeJets
import Calderon.SignedOperatorTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referenceAdjointHalfNativeTaylorNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceAdjointHalfNativeTaylorOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

attribute [local irreducible] referenceAdjointHalfRadialFamily
  referenceLowerRadialEndpointFamily referenceRadialEndpointInvertibleLocus
  secondTaylorRemainder sphereLowerDistributionalTranspose
  sphereSobolevShiftedDegreeL sphereSobolevRadialDriftAdjointL sphereSobolevInclusionL

lemma referenceAdjointHalfRadialFamily_zero_eq_shiftedDegree
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hpFields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hOrd := referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  exact (sphereLowerDistributionalTranspose_referenceLowerRadial
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,0)) hpFields.2.1).symm.trans
      ((congrArg sphereLowerDistributionalTranspose hOrd).trans
        sphereLowerDistributionalTranspose_shiftedDegree_half)

lemma referenceAdjointHalfRadialFamily_signed_native_taylor
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) +
      r • (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) +
      r^2 • secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r := by
  let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun t =>
    referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have hSmooth : ∀ t ∈ uIcc (0 : ℝ) r, ContDiffAt ℝ ∞ A t := by
    intro t ht
    have hJoint := (contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment t ht))
    exact hJoint.comp (f := fun t : ℝ => (q,(y,t))) t
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hZero : A 0 = sphereSobolevShiftedDegreeL (1/2 : ℝ) :=
    referenceAdjointHalfRadialFamily_zero_eq_shiftedDegree
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hFirst : deriv A 0 =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) :=
    deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hTaylor := signed_taylor_integral_remainder A r hSmooth
  have hChange := congrArg₂
    (fun Z D : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      Z + r • D + r^2 • secondTaylorRemainder A r) hZero hFirst
  exact hTaylor.trans hChange

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHalfRadialFamily_signed_native_taylor

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHalfRadialFamily_zero_eq_shiftedDegree
