import Calderon.ReferenceRadiusScaling
import Calderon.MixedKernelConstruction.MixedKernelCylinderBoundary
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The profile root of the actual manuscript radius is uniformly Lipschitz
on one fixed coordinate ball, with its constant chosen before shrinkage. -/
theorem exists_uniform_softplus_referenceDepth_lipschitz_on_closedBall
    (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∀ y ∈ closedBall (0 : R3) 3, ∀ z ∈ closedBall (0 : R3) 3,
        |softplus δ (referenceDepth L z) - softplus δ (referenceDepth L y)| ≤
          C * ‖z - y‖ := by
  obtain ⟨K, hK⟩ :=
    ((contDiff_referenceDepth L).contDiffOn (s := closedBall (0 : R3) 3)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro δ hδ y hy z hz
  have hdiffer : ∀ t ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (softplus δ) t := by
    intro t _
    exact (hasDerivAt_softplus δ t hδ.ne').differentiableAt
  have hderiv : ∀ t ∈ (Set.univ : Set ℝ), ‖deriv (softplus δ) t‖ ≤ (1 : ℝ) := by
    intro t _
    rw [(hasDerivAt_softplus δ t hδ.ne').deriv, Real.norm_eq_abs,
      abs_of_pos (softplus_derivative_pos δ t)]
    exact (softplus_derivative_lt_one δ t).le
  have hs := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    hdiffer hderiv (Set.mem_univ (referenceDepth L y)) (Set.mem_univ (referenceDepth L z))
  have hdepth := hK.dist_le_mul z hz y hy
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at hdepth
  rw [Real.norm_eq_abs] at hs
  calc
    |softplus δ (referenceDepth L z) - softplus δ (referenceDepth L y)| ≤
        |referenceDepth L z - referenceDepth L y| := by simpa using hs
    _ ≤ (K : ℝ) * ‖z - y‖ := by simpa [dist_eq_norm] using hdepth
    _ ≤ ((K : ℝ) + 1) * ‖z - y‖ := by gcongr; linarith

/-- The same delta-independent profile constant controls the actual radius
at two nearby centers, in both directions. -/
theorem exists_uniform_referenceRadius_local_power_comparison
    (L R : ℝ) (p : ℕ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∀ y ∈ closedBall (0 : R3) 3, ∀ z ∈ closedBall (0 : R3) 3,
        C * ‖z - y‖ ≤ (1/2 : ℝ) * softplus δ (referenceDepth L y) →
          (1/2 : ℝ)^p * referenceRadius δ R p L y ≤
            referenceRadius δ R p L z ∧
          referenceRadius δ R p L z ≤
            (3/2 : ℝ)^p * referenceRadius δ R p L y := by
  obtain ⟨C,hC,hLip⟩ := exists_uniform_softplus_referenceDepth_lipschitz_on_closedBall L
  refine ⟨C,hC,?_⟩
  intro δ hδ y hy z hz hsmall
  let uy := softplus δ (referenceDepth L y)
  let uz := softplus δ (referenceDepth L z)
  have huy : 0 < uy := softplus_pos δ _ hδ
  have huz : 0 < uz := softplus_pos δ _ hδ
  have hdiff : |uz - uy| ≤ (1/2 : ℝ) * uy :=
    (hLip δ hδ y hy z hz).trans hsmall
  have hlow : (1/2 : ℝ) * uy ≤ uz := by
    have h := (abs_le.mp hdiff).1
    linarith
  have hupp : uz ≤ (3/2 : ℝ) * uy := by
    have h := (abs_le.mp hdiff).2
    linarith
  have hpowLow : ((1/2 : ℝ) * uy)^p ≤ uz^p :=
    pow_le_pow_left₀ (by positivity) hlow p
  have hpowUpp : uz^p ≤ ((3/2 : ℝ) * uy)^p :=
    pow_le_pow_left₀ huz.le hupp p
  constructor
  · calc
      (1/2 : ℝ)^p * referenceRadius δ R p L y =
          R * ((1/2 : ℝ) * uy)^p := by
            unfold referenceRadius uy
            rw [mul_pow]
            ring
      _ ≤ R * uz^p := mul_le_mul_of_nonneg_left hpowLow hR
      _ = referenceRadius δ R p L z := rfl
  · calc
      referenceRadius δ R p L z = R * uz^p := rfl
      _ ≤ R * ((3/2 : ℝ) * uy)^p := mul_le_mul_of_nonneg_left hpowUpp hR
      _ = (3/2 : ℝ)^p * referenceRadius δ R p L y := by
            unfold referenceRadius uy
            rw [mul_pow]
            ring

/-- A geometric small-distance condition converts the checked global two-power
weighted moment into a local unweighted L² bound on an actual interpolation ball. -/
theorem exists_local_eLpNorm_le_weighted_referenceRadius_moment
    (L R : ℝ) (p : ℕ) (hR : 0 < R)
    (μ : Measure R3) (chi V : R3 → ℝ) (hV : Continuous V) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∀ y ∈ closedBall (0 : R3) 3, ∀ s : ℝ, 0 ≤ s →
        ball y s ⊆ cylinder → ball y s ⊆ closedBall (0 : R3) 3 →
        (∀ z ∈ ball y s, chi z = 1) →
        C * s ≤ (1/2 : ℝ) * softplus δ (referenceDepth L y) →
          eLpNorm V 2 (μ.restrict (ball y s)) ≤
            ENNReal.ofReal (((3/2 : ℝ)^p * referenceRadius δ R p L y)^2) *
              eLpNorm (fun z => chi z * V z /
                (referenceRadius δ R p L z)^2) 2 (μ.restrict cylinder) := by
  obtain ⟨C,hC,hCompare⟩ := exists_uniform_referenceRadius_local_power_comparison L R p hR.le
  refine ⟨C,hC,?_⟩
  intro δ hδ y hy s hs hBallCylinder hBall3 hchi hsmall
  let r : R3 → ℝ := referenceRadius δ R p L
  let b : ℝ := (3/2 : ℝ)^p * r y
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
    (g := fun z => chi z * V z / (r z)^2) hV.aestronglyMeasurable hAE (2 : ℝ≥0∞)
  have hmono : eLpNorm (fun z => chi z * V z / (r z)^2) 2
      (μ.restrict (ball y s)) ≤
      eLpNorm (fun z => chi z * V z / (r z)^2) 2
        (μ.restrict cylinder) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hBallCylinder le_rfl)
  simpa only [b, r] using hlocal.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

end OAI.AnisotropicCalderon.ConformalDepth
