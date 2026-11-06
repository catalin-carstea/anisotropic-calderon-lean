import TauCeti.Analysis.Sobolev.W1p.Multiplication
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-! EXPANSION.json precedes exact local cutoff-value recovery; no global cutoff equality is asserted. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E}

lemma restrict_contDiffSMul_eq_of_value_zero_on_ne_one (hU : U ≤ Omega)
    (eta : E → ℝ) (heta : ContDiff ℝ ∞ eta) {M : ℝ} (hM : 0 ≤ M)
    (hEtaM : ∀ x ∈ Omega, |eta x| ≤ M)
    (hGradM : ∀ x ∈ Omega, ‖∇ eta x‖ ≤ M)
    (w : TauCeti.W1p mu Omega 2)
    (hZero : ∀ᵐ x ∂mu.restrict U, eta x ≠ 1 → TauCeti.W1p.value w x = 0) :
    TauCeti.W1p.restrictL hU (TauCeti.W1p.contDiffSMul eta heta hM hEtaM hGradM w) =
      TauCeti.W1p.restrictL hU w := by
  have hMu : mu.restrict U ≤ mu.restrict Omega :=
    Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  have hProduct := (TauCeti.W1p.value_contDiffSMul_ae heta hM hEtaM hGradM w).filter_mono
    (ae_mono hMu)
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [TauCeti.W1p.value_restrictL_ae hU
      (TauCeti.W1p.contDiffSMul eta heta hM hEtaM hGradM w),
    TauCeti.W1p.value_restrictL_ae hU w,hProduct,hZero] with x hLeft hRight hProd hZ
  rw [hLeft,hRight,hProd,smul_eq_mul]
  by_cases hOne : eta x = 1
  · rw [hOne,one_mul]
  · rw [hZ hOne,mul_zero]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.restrict_contDiffSMul_eq_of_value_zero_on_ne_one
