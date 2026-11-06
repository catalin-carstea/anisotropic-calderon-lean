import Calderon.NativeCoefficientFluxTrace
import Calderon.NativeHalfSmoothMultiplier
import Calderon.NativeNegativeHalfSmoothMultiplier
import Calderon.ClosedCoefficientMultiplier

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient ENNReal
namespace OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeFullSharpHalfTrace NativeHarmonicH1LiftCompletion NativeHalfSmoothMultiplier
  NativeNegativeHalfSmoothMultiplier

def realHilbertOperatorAdjointL
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] :
    (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
  ({ toFun := fun A => ContinuousLinearMap.adjoint A
     map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
     map_smul' := fun c A => by
       simp only [map_smulₛₗ, starRingEnd_apply, star_trivial, RingHom.id_apply] } :
    (V →L[ℝ] V) →ₗ[ℝ] (V →L[ℝ] V)).mkContinuous 1
      (fun A => by
        change ‖ContinuousLinearMap.adjoint A‖ ≤ (1 : ℝ) * ‖A‖
        simpa only [one_mul] using (ContinuousLinearMap.adjoint.norm_map A).le)

def realHalfOperatorAdjointL :
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  realHilbertOperatorAdjointL (SphereSobolev (1/2 : ℝ))

def nativeHalfCoefficientMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 2) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (nativeHalfTraceL hF hO hD τ0).comp
    ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0).comp
      ((coefficientMultiplier hcalc 1 F).comp (harmonicFirstOrderLiftCompletion hF)))

def nativeNegativeHalfCoefficientMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 2) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  realHalfOperatorAdjointL (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F)

lemma nativeHalfCoefficientMulL_eq_smoothMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coefficientSmoothData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coefficientSmoothData F).1 x‖ ≤ M) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg := by
  apply ContinuousLinearMap.ext
  intro f
  change nativeHalfTraceL hF hO hD τ0
    (TauCeti.Wkp.firstOrderL 0 (coefficientMultiplier hcalc 1 F (harmonicFirstOrderLiftCompletion hF f))) = _
  rw [TauCeti.Wkp.firstOrderL_apply]
  have h := firstOrder_coefficientMultiplier_eq_contDiffSMulL hcalc F
    (harmonicFirstOrderLiftCompletion hF f) hM hm hg
  exact congrArg (nativeHalfTraceL hF hO hD τ0) h

lemma nativeNegativeHalfCoefficientMulL_eq_smoothMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coefficientSmoothData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coefficientSmoothData F).1 x‖ ≤ M) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeNegativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg := by
  change ContinuousLinearMap.adjoint (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F) =
    ContinuousLinearMap.adjoint (nativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg)
  exact congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    ContinuousLinearMap.adjoint A)
      (nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg)

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

lemma contDiff_nativeHalfCoefficientMulL_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g : H × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ p x, x ∉ K → g (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : H => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 2 g hg K hK hz p)) := by
  unfold nativeHalfCoefficientMulL
  exact contDiff_const.clm_comp (contDiff_const.clm_comp
    ((contDiff_commonSupport_actual_coefficientMultiplier hcalc 1 g hg K hK hz).clm_comp contDiff_const))

lemma contDiff_nativeNegativeHalfCoefficientMulL_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g : H × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ p x, x ∉ K → g (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : H => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 2 g hg K hK hz p)) := by
  have hAdj : ContDiff ℝ ∞ (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      realHalfOperatorAdjointL A) := by
    apply ContinuousLinearMap.contDiff
  change ContDiff ℝ ∞ (fun p : H => realHalfOperatorAdjointL
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (commonSupportCoefficientFamily 2 g hg K hK hz p)))
  exact hAdj.comp (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 g hg K hK hz)

end OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.realHalfOperatorAdjointL
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeHalfCoefficientMulL
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeNegativeHalfCoefficientMulL
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeHalfCoefficientMulL_eq_smoothMulL
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeNegativeHalfCoefficientMulL_eq_smoothMulL
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.contDiff_nativeHalfCoefficientMulL_commonSupport
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.contDiff_nativeNegativeHalfCoefficientMulL_commonSupport
