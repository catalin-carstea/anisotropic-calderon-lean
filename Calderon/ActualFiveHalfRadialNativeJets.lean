import Calderon.ActualReferenceAdjointFiveHalfRadialCompatibility
import Calderon.ActualReferenceHighAdjointRadialNativeJets
import Calderon.ActualFirstCorrectionSobolevFamilies
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic

theorem sphereSobolevShiftedDegree_fivehalf_threehalf_compatibility
    (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (sphereSobolevShiftedDegreeL (5/2:ℝ) u) =
    sphereSobolevShiftedDegreeL (3/2:ℝ)
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  apply sphereSobolev_ext (1/2:ℝ)
  intro k
  rw [sphereSobolevCoefficientL_inclusion]
  have hHi : sphereSobolevCoefficientL (3/2:ℝ) k (sphereSobolevShiftedDegreeL (5/2:ℝ) u) =
      (k:ℝ) • sphereSobolevCoefficientL (5/2:ℝ) k u := by
    have hIndex := congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
      (sphereSobolevShiftedDegreeL (5/2:ℝ) u)) (show (5/2:ℝ)-1=3/2 by norm_num)
    exact hIndex.symm.trans (sphereSobolevCoefficientL_shiftedDegree (5/2:ℝ) k u)
  have hLo : sphereSobolevCoefficientL (1/2:ℝ) k
      (sphereSobolevShiftedDegreeL (3/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) =
      (k:ℝ) • sphereSobolevCoefficientL (5/2:ℝ) k u := by
    have hIndex := congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
      (sphereSobolevShiftedDegreeL (3/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)))
      (show (3/2:ℝ)-1=1/2 by norm_num)
    exact hIndex.symm.trans ((sphereSobolevCoefficientL_shiftedDegree (3/2:ℝ) k _).trans
      (congrArg (fun z => (k:ℝ) • z)
        (sphereSobolevCoefficientL_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) u k)))
  exact hHi.trans hLo.symm

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  referenceRadialEndpointInvertibleLocus sphereSobolevInclusionL sphereSobolevShiftedDegreeL
  sphereSobolevRadialDriftAdjointL

theorem referenceAdjointFiveHalfRadialFamily_zero_eq_shiftedDegree
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) =
      sphereSobolevShiftedDegreeL (5/2:ℝ) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hpFields := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hComp := referenceAdjointRadialEndpointFamily_fivehalf_threehalf_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) hpFields.2.1
  have hZero := referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) (1/2:ℝ) (by norm_num)
  exact (DFunLike.congr_fun hComp u).trans
    ((congrArg (fun A => A (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) hZero).trans
      (sphereSobolevShiftedDegree_fivehalf_threehalf_compatibility u).symm)

theorem deriv_referenceAdjointFiveHalfRadialFamily_zero_eq_nativeFirstCorrection
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    deriv (fun t : ℝ => referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0 =
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (5/2:ℝ) (referenceCenterDrift g L q y)) := by
  let UH := fun t : ℝ => referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let A := fun t : ℝ => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let I := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let D := sphereSobolevRadialDriftAdjointL hF hO hD (3/2:ℝ) (referenceCenterDrift g L q y)
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hParam : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hHighSmooth : ContDiffAt ℝ ∞ UH 0 :=
    ((contDiffOn_referenceAdjointFiveHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt (hOpen.mem_nhds hp)).comp 0 hParam.contDiffAt
  have hLowSmooth : ContDiffAt ℝ ∞ A 0 :=
    ((contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt (hOpen.mem_nhds hp)).comp 0 hParam.contDiffAt
  have hHigh : HasDerivAt UH (deriv UH 0) 0 := (hHighSmooth.differentiableAt (by simp)).hasDerivAt
  have hLow : HasDerivAt A (J.comp D) 0 :=
    ((hLowSmooth.differentiableAt (by simp)).hasDerivAt).congr_deriv
      (deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy)
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    hParam.continuous.continuousAt.eventually (hOpen.mem_nhds hp)
  apply ContinuousLinearMap.ext
  intro u
  have hHu := hHigh.clm_apply (hasDerivAt_const (0:ℝ) u)
  have hAu := hLow.clm_apply (hasDerivAt_const (0:ℝ) (I u))
  simp only [map_zero,add_zero] at hHu hAu
  have hIncluded := J.hasFDerivAt.comp_hasDerivAt 0 hHu
  have hEq : (fun t => A t (I u)) =ᶠ[𝓝 (0:ℝ)] (fun t => J (UH t u)) := by
    filter_upwards [hNear] with t ht
    have htFields := ht
    unfold referenceRadialEndpointInvertibleLocus at htFields
    exact (DFunLike.congr_fun (referenceAdjointRadialEndpointFamily_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,t)) htFields.2.1) u).symm
  have hSame := hIncluded.congr_of_eventuallyEq hEq
  have hRelation : J ((deriv UH 0) u) = J (D (I u)) := hSame.unique hAu
  have hDCompat := sphereSobolevInclusionL_radialDriftAdjoint hF hO hD
    (5/2:ℝ) (3/2:ℝ) (by norm_num) (referenceCenterDrift g L q y) u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) (1/2:ℝ) (by norm_num)
  exact hRelation.trans (congrArg J hDCompat.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
