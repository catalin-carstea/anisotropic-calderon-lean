import Calderon.ActualReferenceRadiusLocalComparison
import Calderon.ActualReferenceRadiusInterpolationScale

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The exact interpolation-radius L² estimate has one threshold chosen
before the source family, its dilation, the cutoff, the measure and δ. -/
theorem exists_local_eLpNorm_at_referenceRadius_interpolationScale_uniform_continuousOn
    (L R : ℝ) (p : ℕ) (hR : 0 < R) (hp : 24 ≤ p) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ (μ : Measure R3) (chi V : R3 → ℝ), ContinuousOn V cylinder →
      ∀ δ : ℝ, 0 < δ → ∀ y ∈ closedBall (0 : R3) 3,
        let r := referenceRadius δ R p L y
        let s := r ^ ((1 : ℝ) / 23)
        r < rho →
        ball y s ⊆ cylinder → ball y s ⊆ closedBall (0 : R3) 3 →
        (∀ z ∈ ball y s, chi z = 1) →
          eLpNorm V 2 (μ.restrict (ball y s)) ≤
            ENNReal.ofReal (((3/2 : ℝ)^p * r)^2) *
              eLpNorm (fun z => chi z * V z /
                (referenceRadius δ R p L z)^2) 2 (μ.restrict cylinder) := by
  obtain ⟨C,hC,hCompare⟩ :=
    exists_uniform_referenceRadius_local_power_comparison L R p hR.le
  obtain ⟨rho,hrho,hSmall⟩ :=
    exists_referenceRadius_interpolationScale_smallness L R C p hR hC hp
  refine ⟨rho,hrho,?_⟩
  intro μ chi V hV δ hδ y hy
  dsimp
  intro hrsmall hBallCylinder hBall3 hchi
  let r : R3 → ℝ := referenceRadius δ R p L
  let s : ℝ := (r y) ^ ((1 : ℝ) / 23)
  let b : ℝ := (3/2 : ℝ)^p * r y
  have hsmall : C * s ≤ (1/2 : ℝ) * softplus δ (referenceDepth L y) :=
    hSmall δ hδ y hrsmall
  have hAE : ∀ᵐ z ∂(μ.restrict (ball y s)),
      ‖V z‖ ≤ b^2 * ‖chi z * V z / (r z)^2‖ := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    have hdist : ‖z - y‖ ≤ s := by
      have := (mem_ball.mp hz).le
      simpa [dist_eq_norm] using this
    have hsmallZ : C * ‖z - y‖ ≤ (1/2 : ℝ) * softplus δ (referenceDepth L y) :=
      (mul_le_mul_of_nonneg_left hdist hC.le).trans hsmall
    have hrle : r z ≤ b := (hCompare δ hδ y hy z (hBall3 hz) hsmallZ).2
    have hrz : 0 < r z := referenceRadius_pos δ R p L z hδ hR
    have hr2 : (r z)^2 ≤ b^2 := pow_le_pow_left₀ hrz.le hrle 2
    have hscaled : ‖chi z * V z / (r z)^2‖ = ‖V z‖ / (r z)^2 := by
      simp only [hchi z hz, one_mul, norm_div, Real.norm_eq_abs,
        abs_of_pos (pow_pos hrz 2)]
    calc
      ‖V z‖ = (r z)^2 * (‖V z‖ / (r z)^2) := by
        field_simp [ne_of_gt hrz]
      _ ≤ b^2 * (‖V z‖ / (r z)^2) :=
        mul_le_mul_of_nonneg_right hr2 (div_nonneg (norm_nonneg _) (sq_nonneg _))
      _ = b^2 * ‖chi z * V z / (r z)^2‖ := by rw [hscaled]
  have hlocal := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (μ := μ.restrict (ball y s)) (f := V)
    (g := fun z => chi z * V z / (r z)^2) ((hV.mono hBallCylinder).aestronglyMeasurable (μ := μ) isOpen_ball.measurableSet) hAE (2 : ℝ≥0∞)
  have hmono : eLpNorm (fun z => chi z * V z / (r z)^2) 2
      (μ.restrict (ball y s)) ≤
      eLpNorm (fun z => chi z * V z / (r z)^2) 2
        (μ.restrict cylinder) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hBallCylinder le_rfl)
  simpa only [b, r, s] using
    hlocal.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

end OAI.AnisotropicCalderon.ConformalDepth
