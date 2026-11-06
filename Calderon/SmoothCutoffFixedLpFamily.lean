import Calderon.SingularProfileLpParameterCalculus
import Calderon.BoundedParameterSmoothness

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.ConnectionError

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def cutoffCoefficientField (h : P × R3 → ℝ) (χ : R3 → ℝ) : P × R3 → ℝ :=
  fun x => χ x.2 * h x

def cutoffCoefficientBCF (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) :
    P → (R3 →ᵇ ℝ) :=
  CommonSupportSlices.commonSupportSlice (cutoffCoefficientField h χ)
    ((hχ.continuous.comp continuous_snd).mul hh.continuous)
    (tsupport χ) hCompact (by
      intro p z hz
      simp only [cutoffCoefficientField, image_eq_zero_of_notMem_tsupport hz, zero_mul])

def cutoffCoefficientLpFamily (μ : Measure R3) (f : Lp ℝ 2 μ)
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) : P → Lp ℝ 2 μ :=
  fun p => boundedContinuousMulLpL μ f (cutoffCoefficientBCF h hh χ hχ hCompact p)

theorem contDiff_cutoffCoefficientField
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h) (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (cutoffCoefficientField h χ) := by
  exact (hχ.comp contDiff_snd).mul hh

theorem cutoffCoefficientField_zero_outside_tsupport
    (h : P × R3 → ℝ) (χ : R3 → ℝ) (p : P) (z : R3) (hz : z ∉ tsupport χ) :
    cutoffCoefficientField h χ (p,z) = 0 := by
  simp only [cutoffCoefficientField, image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem cutoffCoefficientBCF_apply
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (p : P) (z : R3) :
    cutoffCoefficientBCF h hh χ hχ hCompact p z = χ z * h (p,z) := by
  rfl

theorem contDiff_cutoffCoefficientBCF
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) :
    ContDiff ℝ ∞ (cutoffCoefficientBCF h hh χ hχ hCompact) := by
  exact BoundedParameterSmoothness.contDiff_infty_commonSupportSlice
    (cutoffCoefficientField h χ) (contDiff_cutoffCoefficientField h hh χ hχ)
    (tsupport χ) hCompact (cutoffCoefficientField_zero_outside_tsupport h χ)

theorem cutoffCoefficientLpFamily_ae
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (p : P) :
    cutoffCoefficientLpFamily μ f h hh χ hχ hCompact p =ᵐ[μ]
      (fun z => χ z * h (p,z) * f z) := by
  simpa only [cutoffCoefficientLpFamily, cutoffCoefficientBCF_apply] using
    boundedContinuousMulLpL_apply_ae μ f (cutoffCoefficientBCF h hh χ hχ hCompact p)

theorem contDiff_cutoffCoefficientLpFamily
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) :
    ContDiff ℝ ∞ (cutoffCoefficientLpFamily μ f h hh χ hχ hCompact) := by
  exact contDiff_boundedContinuousMulLpL_comp μ f
    (cutoffCoefficientBCF h hh χ hχ hCompact) (contDiff_cutoffCoefficientBCF h hh χ hχ hCompact)

theorem norm_cutoffCoefficientLpFamily_le
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (p : P) :
    ‖cutoffCoefficientLpFamily μ f h hh χ hχ hCompact p‖ ≤
      ‖cutoffCoefficientBCF h hh χ hχ hCompact p‖ * ‖f‖ := by
  calc
    _ ≤ ‖boundedContinuousMulLpL μ f‖ * ‖cutoffCoefficientBCF h hh χ hχ hCompact p‖ :=
      (boundedContinuousMulLpL μ f).le_opNorm _
    _ ≤ ‖f‖ * ‖cutoffCoefficientBCF h hh χ hχ hCompact p‖ :=
      mul_le_mul_of_nonneg_right (norm_boundedContinuousMulLpL_le μ f) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem exists_compact_uniform_cutoffCoefficientBCF_bound
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (K : Set P) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ K, ‖cutoffCoefficientBCF h hh χ hχ hCompact p‖ ≤ C := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (contDiff_cutoffCoefficientBCF h hh χ hχ hCompact).continuous.continuousOn
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro p hp
  exact (hB p hp).trans (le_max_left _ _)

theorem exists_compact_uniform_cutoffCoefficientLpFamily_bound
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (K : Set P) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ K,
      ‖cutoffCoefficientLpFamily μ f h hh χ hχ hCompact p‖ ≤ C * ‖f‖ := by
  obtain ⟨C,hC,hBound⟩ := exists_compact_uniform_cutoffCoefficientBCF_bound h hh χ hχ hCompact K hK
  refine ⟨C,hC,?_⟩
  intro p hp
  exact (norm_cutoffCoefficientLpFamily_le μ f h hh χ hχ hCompact p).trans
    (mul_le_mul_of_nonneg_right (hBound p hp) (norm_nonneg f))

theorem exists_compact_uniform_cutoffCoefficientLpFamily_norm_bound
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (h : P × R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (K : Set P) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ K,
      ‖cutoffCoefficientLpFamily μ f h hh χ hχ hCompact p‖ ≤ C := by
  obtain ⟨C,hC,hBound⟩ := exists_compact_uniform_cutoffCoefficientLpFamily_bound
    μ f h hh χ hχ hCompact K hK
  refine ⟨max (C*‖f‖) 1, le_max_right _ _, ?_⟩
  intro p hp
  exact (hBound p hp).trans (le_max_left _ _)

end OAI.AnisotropicCalderon.ConnectionError
