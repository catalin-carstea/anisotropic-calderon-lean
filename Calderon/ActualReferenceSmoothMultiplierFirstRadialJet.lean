import Calderon.ActualReferenceSmoothMultiplierLocalRealization
import Calderon.ActualReferenceSmoothMultiplierLowerCommutator
import Calderon.ActualReferenceEndpointFirstRadialJetMatching

/-! The actual scalar multiplier is held fixed in the radial derivative; the linear
subtraction is proved. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricVolume NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier
attribute [local irreducible] referenceSmoothMultiplierBoundaryCommutatorFamily
  nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL sphereSobolevRadialDriftL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma contDiffAt_referenceSmoothMultiplierBoundaryCommutatorFamily_fixed
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q) p := by
  exact contDiffAt_referenceSmoothMultiplierBoundaryCommutator_of_joint_on_open
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel
    (fun z : (ℝ × (R3 × ℝ)) × R3 => coefficientValue 3 Q z.2) Set.univ isOpen_univ
    (((contDiff_coefficientValue 3 Q).comp contDiff_snd).contDiffOn) (fun _ => Q)
    (fun u hu x => rfl) p (fun x => Set.mem_univ _) hp

lemma radialFirstDerivative_referenceSmoothMultiplierBoundaryCommutator_eq_firstCorrectionCommutator
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (Q : SmoothCoefficientJets 3)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (s,p)) (y,0) =
      (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y)).comp
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)) -
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)).comp
        (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y)) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg s hs y hy
  let F := fun p : R3 × ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (s,p)
  let A := fun p : R3 × ℝ => referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,p)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let M := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let Mn := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let D0 := sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y)
  have hFS := (contDiffAt_referenceSmoothMultiplierBoundaryCommutatorFamily_fixed
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q (s,(y,0)) hp).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hAS := (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,0)) hp.2.2 hp.2.1).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hc : HasDerivAt (fun r : ℝ => (y,r)) (0,1) 0 :=
    (hasDerivAt_const 0 y).prodMk (hasDerivAt_id 0)
  have hFd : HasDerivAt (fun r : ℝ => F (y,r)) (radialFirstDerivative F (y,0)) 0 := by
    simpa only [Function.comp_def,radialFirstDerivative] using
      (hFS.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hAd : HasDerivAt (fun r : ℝ => A (y,r)) (radialFirstDerivative A (y,0)) 0 := by
    simpa only [Function.comp_def,radialFirstDerivative] using
      (hAS.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hNear : ∀ᶠ r : ℝ in 𝓝 0, (s,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  have hA0 : radialFirstDerivative A (y,0) = J.comp D0 :=
    radialFirstDerivative_referenceLowerRadialTrace_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg s hs y hy
  have hA0v (v : SphereSobolev (1/2 : ℝ)) : radialFirstDerivative A (y,0) v = J (D0 v) :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v) hA0
  have hMJ (v : SphereSobolev (1/2 : ℝ)) : Mn (J v) = J (M v) :=
    (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))).symm
  apply ContinuousLinearMap.ext
  intro f
  have hFf := hFd.clm_apply (hasDerivAt_const (0 : ℝ) f)
  have hAMf := hAd.clm_apply (hasDerivAt_const (0 : ℝ) (M f))
  have hAf := hAd.clm_apply (hasDerivAt_const (0 : ℝ) f)
  simp only [map_zero,add_zero,zero_add] at hFf hAMf hAf
  have hJF := J.hasFDerivAt.comp_hasDerivAt 0 hFf
  have hMA := Mn.hasFDerivAt.comp_hasDerivAt 0 hAf
  have hRhs := hAMf.sub hMA
  have hEq : (fun r : ℝ => J (F (y,r) f)) =ᶠ[𝓝 0]
      (fun r : ℝ => A (y,r) (M f)-Mn (A (y,r) f)) := by
    filter_upwards [hNear] with r hr
    exact referenceSmoothMultiplierBoundaryCommutatorFamily_lower_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q (s,(y,r)) hr f
  have hJet : J (radialFirstDerivative F (y,0) f) =
      radialFirstDerivative A (y,0) (M f)-Mn (radialFirstDerivative A (y,0) f) :=
    hJF.unique (hRhs.congr_of_eventuallyEq hEq)
  have hNative := (congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x-y)
    (hA0v (M f)) (congrArg Mn (hA0v f))).trans
      (congrArg (fun z => J (D0 (M f))-z) (hMJ (D0 f)))
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  exact hJet.trans (hNative.trans ((J.map_sub (D0 (M f)) (M (D0 f))).symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSmoothMultiplierBoundaryCommutatorFamily_fixed
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceSmoothMultiplierBoundaryCommutator_eq_firstCorrectionCommutator
