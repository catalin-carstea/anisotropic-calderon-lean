import Calderon.NativeH2SmoothMultiplierDerivative
import Calderon.CoefficientFirstJetsCommonSupport

/-! Joint spatial
derivative with the SAME actual compact support and exact jet transport. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def smoothMultiplierSpatialDerivative (q : P × R3 → ℝ) (i : Fin 3) : P × R3 → ℝ :=
  fun z => fderiv ℝ q z (0,coordinateVector i)

lemma contDiff_smoothMultiplierSpatialDerivative
    (q : P × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (i : Fin 3) :
    ContDiff ℝ ∞ (smoothMultiplierSpatialDerivative q i) :=
  (hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma smoothMultiplierSpatialDerivative_eq_slice_gradient
    (q : P × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (i : Fin 3) (t : P) (x : R3) :
    smoothMultiplierSpatialDerivative q i (t,x) =
      (gradient (fun y : R3 => q (t,y)) x) i := by
  have hqD : DifferentiableAt ℝ q (t,x) := hq.differentiable (by simp) (t,x)
  have hslice := hqD.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hv := congrArg (fun A : R3 →L[ℝ] ℝ => A (coordinateVector i)) hslice.fderiv
  simp only [MetricVolume.gradient_coordinate]
  change fderiv ℝ q (t,x) (0,coordinateVector i) =
    fderiv ℝ (fun y : R3 => q (t,y)) x (coordinateVector i)
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply] using hv.symm

lemma smoothMultiplierSpatialDerivative_zero_outside
    (q : P × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → q (t,x) = 0) (i : Fin 3) :
    ∀ t x, x ∉ K → smoothMultiplierSpatialDerivative q i (t,x) = 0 := by
  intro t x hx
  have hnot : x ∉ tsupport (fun y : R3 => q (t,y)) := by
    intro hs
    exact hx (SpatialJetFields.tsupport_spatial_slice_subset q K hK hz t hs)
  have hd : fderiv ℝ (fun y : R3 => q (t,y)) x = 0 := by
    by_contra hn
    exact hnot (support_fderiv_subset ℝ hn)
  rw [smoothMultiplierSpatialDerivative_eq_slice_gradient q hq i t x,
    MetricVolume.gradient_coordinate,hd]
  rfl

lemma smoothMultiplierLowerJets_commonSupport
    (q : P × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → q (t,x) = 0) (t : P) :
    smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 q hq K hK hz t) =
      commonSupportCoefficientFamily 2 q hq K hK hz t := by
  apply smoothCoefficientJets_eq_of_coefficientValue_eq 2
  funext x
  rw [coefficientValue_smoothMultiplierLowerJets]
  rw [coefficientValue_commonSupportCoefficientFamily,coefficientValue_commonSupportCoefficientFamily]

lemma smoothMultiplierDerivativeJets_commonSupport
    (q : P × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → q (t,x) = 0) (i : Fin 3) (t : P) :
    smoothMultiplierDerivativeJets (commonSupportCoefficientFamily 3 q hq K hK hz t) i =
      commonSupportCoefficientFamily 2 (smoothMultiplierSpatialDerivative q i)
        (contDiff_smoothMultiplierSpatialDerivative q hq i) K hK
        (smoothMultiplierSpatialDerivative_zero_outside q hq K hK hz i) t := by
  apply smoothCoefficientJets_eq_of_coefficientValue_eq 2
  funext x
  rw [coefficientValue_smoothMultiplierDerivativeJets,coefficientValue_commonSupportCoefficientFamily]
  have hv : coefficientValue 3 (commonSupportCoefficientFamily 3 q hq K hK hz t) =
      fun y : R3 => q (t,y) := by
    funext y
    exact coefficientValue_commonSupportCoefficientFamily 3 q hq K hK hz t y
  have hg := congrArg (fun f : R3 → ℝ => (gradient f x) i) hv
  exact hg.trans (smoothMultiplierSpatialDerivative_eq_slice_gradient q hq i t x).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierSpatialDerivative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_smoothMultiplierSpatialDerivative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierSpatialDerivative_eq_slice_gradient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierSpatialDerivative_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierLowerJets_commonSupport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierDerivativeJets_commonSupport
