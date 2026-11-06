import Calderon.NativeLowerTransposeSignedTaylor
import Calderon.ActualReferenceRadialEndpointInvertibleTopology

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-adjoint-signed-remainder-v017.md. SAME independently defined genuine adjoint. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

attribute [local irreducible] referenceLowerRadialEndpointFamily referenceAdjointHalfRadialFamily
  secondTaylorRemainder sphereLowerDistributionalTranspose

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ s ∈ Icc (0 : ℝ) 1, (q,(y,s*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r =
    sphereLowerDistributionalTranspose (secondTaylorRemainder
      (fun t : ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) := by
  let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun t =>
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let S : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun t =>
    referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hOpen : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSlice : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hA : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ A (s*r) := by
    intro s hs
    have hp := hSegment s hs
    have hJoint := contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s*r)) hp.2.2 hp.2.1
    simpa only [A,Function.comp_def] using hJoint.comp (s*r) hSlice.contDiffAt
  have hEq : ∀ s ∈ Icc (0 : ℝ) 1,
      S =ᶠ[𝓝 (s*r)] (fun t => sphereLowerDistributionalTranspose (A t)) := by
    intro s hs
    have hNear : ∀ᶠ t in 𝓝 (s*r), (q,(y,t)) ∈ Ω :=
      hSlice.continuous.continuousAt.eventually (hOpen.mem_nhds (hSegment s hs))
    filter_upwards [hNear] with t ht
    exact (sphereLowerDistributionalTranspose_referenceLowerRadial
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,t)) ht.2.1).symm
  exact (secondTaylorRemainder_eq_of_locallyEq_on_segment S
    (fun t => sphereLowerDistributionalTranspose (A t)) r hEq).trans
      (sphereLowerDistributionalTranspose_secondTaylorRemainder A r hA).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
