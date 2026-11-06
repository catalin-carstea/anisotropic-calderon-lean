import Calderon.NativeRadialJetTranspose
import Calderon.NativeLowerTransposeDerivative
import Calderon.ActualReferenceEndpointFirstRadialJetMatching
import Calderon.ActualReferenceSharpMidpointRadialCoefficients
import Calderon.ActualReferenceAdjointRadialEndpointFamilies
import Calderon.ActualReferenceRadialEndpointInvertibleTopology

/-! Full upfront: full-physical-U-form-author-oct16-v001/
native-adjoint-radial-jets-author-v001/EXPANSION.md. Derive actual B and true
first adjoint jet from the local genuine transpose graph, not a jet premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SpectralWeightedGraph

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceLowerRadialEndpointFamily
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpMidpointRadialTraceFamily referenceRadialEndpointInvertibleLocus
  sphereLowerDistributionalTranspose sphereLowerDistributionalTransposeL

lemma referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) = sphereSobolevShiftedDegreeL (1/2 : ℝ) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hMid := referenceSharpMidpointRadialTrace_zero_eq_degree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hCompat := referenceSharpMidpointRadialTraceFamily_lower_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp
  let I := sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)
  let A := referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0))
  let Bhalf : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevShiftedDegreeL (1/2 : ℝ)
  have hDense (f : SphereSobolev 1) : A (I f) = Bhalf (I f) := by
    have he := congrArg (fun T : SphereSobolev 1 →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => T f) hCompat
    have hPhysical : A (I f) = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevDegreeL f) := by
      have hm := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T f) hMid
      exact he.symm.trans (congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) hm)
    apply sphereSobolev_ext (-(1/2 : ℝ))
    intro k
    have hDegree : sphereSobolevCoefficientL 0 k (sphereSobolevDegreeL f) =
        (k : ℝ) • sphereSobolevCoefficientL 1 k f := by
      have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
        (sphereSobolevShiftedDegreeL 1 f)) (show (1 : ℝ)-1 = 0 by norm_num)
      have hValue := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
        sphereSobolevCoefficientL 0 k (T f)) sphereSobolevShiftedDegreeL_one_eq_degree
      exact hValue.symm.trans
        (hIndex.symm.trans (sphereSobolevCoefficientL_shiftedDegree 1 k f))
    have hHalf : sphereSobolevCoefficientL (-(1/2 : ℝ)) k (Bhalf (I f)) =
        (k : ℝ) • sphereSobolevCoefficientL (1/2 : ℝ) k (I f) := by
      have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (I f)))
        (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
      exact hIndex.symm.trans
        (sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k (I f))
    exact (congrArg (sphereSobolevCoefficientL (-(1/2 : ℝ)) k) hPhysical).trans
      ((sphereSobolevCoefficientL_inclusion 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevDegreeL f) k).trans
        (hDegree.trans (hHalf.trans (congrArg (fun z : harmonicSphereSubspace k => (k : ℝ) • z)
          (sphereSobolevCoefficientL_inclusion 1 (1/2 : ℝ) (by norm_num) f k))).symm))
  apply ContinuousLinearMap.ext
  intro u
  exact denseRange_clm_apply_eq I (denseRange_sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num))
    A Bhalf hDense u

lemma deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    deriv (fun t : ℝ => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0 =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) := by
  let P : R3 × ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    fun p => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)
  let A := fun t : ℝ => P (y,t)
  let S := fun t : ℝ => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let D := sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hpFields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hJoint : ContDiffAt ℝ ∞ P (y,0) :=
    (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hpFields.2.2 hpFields.2.1).comp (y,0)
      (contDiffAt_const.prodMk contDiffAt_id)
  have hSlice : ContDiffAt ℝ ∞ A 0 :=
    hJoint.comp (f := fun t : ℝ => (y,t)) 0
      (contDiffAt_const.prodMk contDiffAt_id)
  have hDeriv : deriv A 0 = J.comp D :=
    (deriv_radialSlice_of_differentiableAt P y 0 (hJoint.differentiableAt (by simp))).trans
      (radialFirstDerivative_referenceLowerRadialTrace_eq_nativeFirstCorrection
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy)
  have hA : HasDerivAt A (J.comp D) 0 :=
    ((hSlice.differentiableAt (by simp)).hasDerivAt).congr_deriv hDeriv
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hParam : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    hParam.continuous.continuousAt.eventually (hOpen.mem_nhds hp)
  have hEq : S =ᶠ[𝓝 (0 : ℝ)] (fun t => sphereLowerDistributionalTranspose (A t)) := by
    filter_upwards [hNear] with t ht
    have htFields : (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := ht
    unfold referenceRadialEndpointInvertibleLocus at htFields
    exact (sphereLowerDistributionalTranspose_referenceLowerRadial
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,t)) htFields.2.1).symm
  have hT := sphereLowerDistributionalTranspose_hasDerivAt A (J.comp D) 0 hA
  have hS := hT.congr_of_eventuallyEq hEq
  have hValue : sphereLowerDistributionalTranspose (J.comp D) =
      J.comp (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ)
        (referenceCenterDrift g L q y)) :=
    sphereLowerDistributionalTranspose_inclusion_radialDrift hF hO hD (referenceCenterDrift g L q y)
  exact hS.deriv.trans hValue

lemma referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) = sphereSobolevShiftedDegreeL (3/2 : ℝ) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hpFields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hOrd := referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hLow : referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) = sphereSobolevShiftedDegreeL (1/2 : ℝ) :=
    (sphereLowerDistributionalTranspose_referenceLowerRadial
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,0)) hpFields.2.1).symm.trans
      ((congrArg sphereLowerDistributionalTranspose hOrd).trans
        sphereLowerDistributionalTranspose_shiftedDegree_half)
  have hCompat := referenceAdjointRadialEndpointFamily_high_half_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) hpFields.2.1
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hv := congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => T u) hCompat
  have hn := congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => T u) sphereSobolevShiftedDegree_high_half_compatibility
  exact hv.trans ((congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => T
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)) hLow).trans hn.symm)

lemma deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0 =
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (3/2 : ℝ) (referenceCenterDrift g L q y)) := by
  let UH := fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let A := fun t : ℝ => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let D := sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hParam : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hHighSmooth : ContDiffAt ℝ ∞ UH 0 :=
    ((contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt (hOpen.mem_nhds hp)).comp 0 hParam.contDiffAt
  have hLowSmooth : ContDiffAt ℝ ∞ A 0 :=
    ((contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt (hOpen.mem_nhds hp)).comp 0 hParam.contDiffAt
  have hHigh : HasDerivAt UH (deriv UH 0) 0 := (hHighSmooth.differentiableAt (by simp)).hasDerivAt
  have hLowValue : deriv A 0 = J.comp D :=
    deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hLow : HasDerivAt A (J.comp D) 0 :=
    ((hLowSmooth.differentiableAt (by simp)).hasDerivAt).congr_deriv hLowValue
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    hParam.continuous.continuousAt.eventually (hOpen.mem_nhds hp)
  apply ContinuousLinearMap.ext
  intro u
  have hHu := hHigh.clm_apply (hasDerivAt_const (0 : ℝ) u)
  have hAu := hLow.clm_apply (hasDerivAt_const (0 : ℝ) (I u))
  simp only [map_zero,add_zero] at hHu hAu
  have hIncluded := J.hasFDerivAt.comp_hasDerivAt 0 hHu
  have hEq : (fun t => A t (I u)) =ᶠ[𝓝 (0 : ℝ)] (fun t => J (UH t u)) := by
    filter_upwards [hNear] with t ht
    have htFields : (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := ht
    unfold referenceRadialEndpointInvertibleLocus at htFields
    exact (congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => T u)
        (referenceAdjointRadialEndpointFamily_high_half_compatibility
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,t)) htFields.2.1)).symm
  have hSame := hIncluded.congr_of_eventuallyEq hEq
  have hRelation : J ((deriv UH 0) u) = J (D (I u)) := hSame.unique hAu
  have hC := sphereSobolevInclusionL_radialDriftAdjoint hF hO hD
    (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (referenceCenterDrift g L q y) u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  exact hRelation.trans (congrArg J hC.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
