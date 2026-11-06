import Calderon.ActualReferenceSharpMidpointRadialDerivativeTransport
import Calderon.ActualReferenceGaugeNormalMultiplierFirstJet
import Calderon.ActualReferenceRadialEndpointInvertibleTopology

/-! Actual derivative certificates; no K jet is assumed. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceLowerRadialEndpointFamily
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily
  referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  referenceGaugeNormalHalfMultiplierFamily

lemma hasDerivAt_referenceLowerRadialEndpoint_radial_zero
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    HasDerivAt (fun r : ℝ => referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)))
      (deriv (fun r : ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0) 0 := by
  let A : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun r =>
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
  have hRoom := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  unfold referenceRadialEndpointInvertibleLocus at hRoom
  have hSmooth : ContDiffAt ℝ ∞ A 0 :=
    (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hRoom.2.2 hRoom.2.1).comp
        (f := fun r : ℝ => (q,(y,r))) 0
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hDiff : DifferentiableAt ℝ A 0 := hSmooth.differentiableAt (by simp)
  exact hDiff.hasFDerivAt.hasDerivAt

lemma referenceGaugeNormalHalfInverse_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) :
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0))).inverse =
      ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) ∧
    HasDerivAt (fun r : ℝ => (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))).inverse)
      (deriv (fun r : ℝ => (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))).inverse) 0) 0 := by
  let P : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun r =>
    referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
  let W : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun r => (P r).inverse
  have hP0 := (referenceGaugeNormalHalfMultiplierFamily_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 q hq y hy).1
  have hW0 : W 0 = ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
    have hi := (referenceGaugeNormalMultiplierFamilies_isInvertible
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0))).1
    apply ContinuousLinearMap.ext
    intro u
    have h := hi.self_apply_inverse u
    have hOuter := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T (W 0 u)) hP0
    exact hOuter.symm.trans h
  have hSlice : ContDiff ℝ ∞ (fun r : ℝ => (q,(y,r))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hSmooth : ContDiff ℝ ∞ W :=
    (contDiff_referenceGaugeNormalHalfMultiplierFamily_inverse
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).comp hSlice
  have hDiff : DifferentiableAt ℝ W 0 := hSmooth.differentiable (by simp) 0
  exact ⟨hW0,hDiff.hasFDerivAt.hasDerivAt⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasDerivAt_referenceLowerRadialEndpoint_radial_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHalfInverse_zero_radial_jet
