import Calderon.ActualReferenceFirstRadialJetMatching
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-actual-endpoint-firstjet-transport-v026.md. Differentiation of
SAME chosen actual endpoint compatibility, then decoded injective/dense inclusion. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma radialFirstDerivative_referenceSharpRadialTrace_midpoint_link
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3)
    (hp : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (3/2 : ℝ)) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0)
      (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f) =
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (radialFirstDerivative (fun p : R3 × ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) f) := by
  have hM := (contDiffAt_referenceSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hU := (contDiffAt_referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp.1).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hNear : ∀ᶠ r : ℝ in 𝓝 0, (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  have hEq : (fun r : ℝ => referenceSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
        (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f)) =ᶠ[𝓝 0]
      (fun r => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 (q,(y,r)) f)) := by
    filter_upwards [hNear] with r hr
    exact congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 => A f)
      (referenceSharpMidpointRadialTraceFamily_upper_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) hr)
  exact radialFirstDerivative_eq_of_linked_evaluation _ _
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)) y
    (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f) f
    (hM.differentiableAt (by simp)) (hU.differentiableAt (by simp)) hEq

lemma radialFirstDerivative_referenceSharpRadialTrace_eq_nativeFirstCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) =
      (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hm := radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  let d := referenceCenterDrift g L q y
  apply ContinuousLinearMap.ext
  intro f
  have hLink := radialFirstDerivative_referenceSharpRadialTrace_midpoint_link
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y hp f
  have hMid := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    A (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f)) hm
  have hIn1 := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 => A f)
    (sphereSobolevInclusionL_trans (3/2 : ℝ) 1 0 (by norm_num) (by norm_num))
  have hInHalf := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 => A f)
    (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) 0 (by norm_num) (by norm_num))
  have hN1 := sphereSobolevInclusionL_radialDrift hF hO hD 1 0 (by norm_num) d
    (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f)
  have hNH := sphereSobolevInclusionL_radialDrift hF hO hD (1/2 : ℝ) 0 (by norm_num) d
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)
  have hNative := hN1.trans ((congrArg (sphereSobolevRadialDriftL hF hO hD 0 d)
    (hIn1.trans hInHalf.symm)).trans hNH.symm)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  exact hLink.symm.trans (hMid.trans hNative)

lemma radialFirstDerivative_referenceLowerRadialTrace_midpoint_link
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3)
    (hp : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev 1) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0)
      (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) f) := by
  have hM := (contDiffAt_referenceSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hU := (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp.2.2 hp.2.1).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hNear : ∀ᶠ r : ℝ in 𝓝 0, (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  have hEq : (fun r : ℝ => referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
        (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) f)) =ᶠ[𝓝 0]
      (fun r => sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 (q,(y,r)) f)) := by
    filter_upwards [hNear] with r hr
    exact (congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
      (referenceSharpMidpointRadialTraceFamily_lower_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) hr)).symm
  exact radialFirstDerivative_eq_of_linked_evaluation _ _
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) y
    (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) f) f
    (hU.differentiableAt (by simp)) (hM.differentiableAt (by simp)) hEq

lemma radialFirstDerivative_referenceLowerRadialTrace_eq_nativeFirstCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hm := radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  let d := referenceCenterDrift g L q y
  let I := sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
  let A := radialFirstDerivative (fun p : R3 × ℝ => referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0)
  let D := (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
    (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d)
  have hDense (f : SphereSobolev 1) : A (I f) = D (I f) := by
    have hLink := radialFirstDerivative_referenceLowerRadialTrace_midpoint_link
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y hp f
    have hMid := congrArg (fun M : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => M f) hm
    have hOut0 := congrArg (fun M : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      M (sphereSobolevRadialDriftL hF hO hD 1 d f))
      (sphereSobolevInclusionL_trans 1 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
    have hOutHalf := congrArg (fun M : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      M (sphereSobolevRadialDriftL hF hO hD 1 d f))
      (sphereSobolevInclusionL_trans 1 (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (by norm_num))
    have hNat := congrArg (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
      (sphereSobolevInclusionL_radialDrift hF hO hD 1 (1/2 : ℝ) (by norm_num) d f)
    exact hLink.trans ((congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) hMid).trans
      ((hOut0.trans hOutHalf.symm).trans hNat))
  apply ContinuousLinearMap.ext
  intro f
  exact denseRange_clm_apply_eq I (denseRange_sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num))
    A D hDense f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceSharpRadialTrace_midpoint_link
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceSharpRadialTrace_eq_nativeFirstCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceLowerRadialTrace_midpoint_link
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceLowerRadialTrace_eq_nativeFirstCorrection
