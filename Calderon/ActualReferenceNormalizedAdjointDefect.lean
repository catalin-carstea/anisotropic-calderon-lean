import Calderon.ActualReferenceGaugeHalfTangentDefect
import Calderon.ActualReferenceGaugeTangentSecondDefect
import Calderon.ActualReferenceGaugeNormalHalfRemainder
import Calderon.ActualReferenceLowerRadialTraceSecondRemainder
import Calderon.ActualReferenceAdjointRadialSignedRemainder
import Calderon.SignedTaylorQuadraticFactor
import Calderon.SignedTaylorAdditiveTransport

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-normalized-adjoint-defect-v022.md. SAME signed integral remainders. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance instCompleteSpaceNormalizedAdjointDefectHalf : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance instCompleteSpaceNormalizedAdjointDefectNegative : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

attribute [local irreducible] referenceLowerRadialEndpointFamily referenceAdjointHalfRadialFamily
  referenceGaugeNormalHalfCommutatorFamily referenceGaugeTangentSecondDefectFamily
  referenceLowerRadialTraceSecondRemainder referenceGaugeNormalHalfSecondRemainder
  secondTaylorRemainder sphereLowerDistributionalTranspose referenceRadialEndpointInvertibleLocus

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

theorem referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_normal_add_tangent
    (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    sphereLowerDistributionalTranspose (referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r) -
      referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r =
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeNormalHalfSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r) +
      referenceGaugeTangentSecondDefectFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) := by
  letI : NormedAddCommGroup (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  let A := fun t : ℝ => referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let S := fun t : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let K := fun t : ℝ => referenceGaugeNormalHalfCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))
  let U := fun t : ℝ => referenceGaugeTangentSecondDefectFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let postLinear : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    { toFun := fun T => J.comp T
      map_add' := fun T V => by
        apply ContinuousLinearMap.ext
        intro u
        exact J.map_add (T u) (V u)
      map_smul' := fun c T => by
        apply ContinuousLinearMap.ext
        intro u
        exact J.map_smul c (T u) }
  let Post : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    LinearMap.mkContinuous postLinear ‖J‖ (fun T => J.opNorm_comp_le T)
  have hPostApply (T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :
      Post T = J.comp T := rfl
  let Ω := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hOpen : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSlice : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hA (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) := by
    have hp := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hp
    exact (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,θ*r)) hp.2.2 hp.2.1).comp
        (f := fun t : ℝ => (q,(y,t))) (θ*r) hSlice.contDiffAt
  have hS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) := by
    have hJoint := (contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
        (hOpen.mem_nhds (hSegment θ hθ))
    exact hJoint.comp (f := fun t : ℝ => (q,(y,t))) (θ*r) hSlice.contDiffAt
  have hK (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ K (θ*r) :=
    (contDiffAt_referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,θ*r)) (hSegment θ hθ)).comp
        (f := fun t : ℝ => (q,(y,t))) (θ*r) hSlice.contDiffAt
  have hU : ContDiff ℝ ∞ U := (contDiff_referenceGaugeTangentSecondDefectFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0).comp hSlice
  have hEq : ∀ θ ∈ Icc (0 : ℝ) 1,
      (fun t => S t-A t) =ᶠ[𝓝 (θ*r)] (fun t => Post (K t)+t^2 • U t) := by
    intro θ hθ
    have hNear : ∀ᶠ t : ℝ in 𝓝 (θ*r), (q,(y,t)) ∈ Ω :=
      hSlice.continuous.continuousAt.eventually (hOpen.mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with t ht
    have htFields : (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := ht
    unfold referenceRadialEndpointInvertibleLocus at htFields
    have hTranspose : sphereLowerDistributionalTranspose (A t) = S t :=
      sphereLowerDistributionalTranspose_referenceLowerRadial
        g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,t)) htFields.2.1
    have hDefect : sphereLowerDistributionalTranspose (A t)-A t = Post (K t)+t^2 • U t := by
      have hRaw := referenceLowerRadialEndpoint_distributionalTranspose_sub_eq_half_add_tangent_second
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel q hq y hy t ht
      unfold U referenceGaugeTangentSecondDefectFamily
      simpa only [hPostApply,A,K,J] using hRaw
    exact (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => Z-A t) hTranspose).symm.trans hDefect
  have hSame := secondTaylorRemainder_eq_of_locallyEq_on_segment
    (fun t => S t-A t) (fun t => Post (K t)+t^2 • U t) r hEq
  have hLeft := secondTaylorRemainder_sub S A r hS hA
  have hAdjoint : secondTaylorRemainder S r =
      sphereLowerDistributionalTranspose (secondTaylorRemainder A r) :=
    secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hLeft' : secondTaylorRemainder (fun t => S t-A t) r =
      sphereLowerDistributionalTranspose (secondTaylorRemainder A r)-secondTaylorRemainder A r :=
    hLeft.trans (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => Z-secondTaylorRemainder A r) hAdjoint)
  have hPost (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun t => Post (K t)) (θ*r) :=
    by
      have hFixed : ContDiffAt ℝ ∞ (fun t : ℝ => J.comp (K t)) (θ*r) :=
        contDiffAt_const.clm_comp (hK θ hθ)
      simpa only [hPostApply] using hFixed
  have hQuad (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun t : ℝ => t^2 • U t) (θ*r) :=
    (contDiffAt_id.pow 2).smul hU.contDiffAt
  have hRight := secondTaylorRemainder_add (fun t => Post (K t))
    (fun t : ℝ => t^2 • U t) r hPost hQuad
  have hMap := secondTaylorRemainder_fixed_linear_map K Post r hK
  have hFactor := secondTaylorRemainder_sq_smul U r (fun t _ => hU.contDiffAt)
  have hRight' : secondTaylorRemainder (fun t => Post (K t)+t^2 • U t) r =
      Post (secondTaylorRemainder K r)+U r :=
    hRight.trans (congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => x+y) hMap.symm hFactor)
  unfold referenceLowerRadialTraceSecondRemainder referenceGaugeNormalHalfSecondRemainder
  exact hLeft'.symm.trans (hSame.trans hRight')

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_normal_add_tangent
