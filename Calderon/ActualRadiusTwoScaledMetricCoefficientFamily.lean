import Calderon.RadiusTwoNativeSourceFoundation
import Calderon.NativeSmoothBallSobolev
import Calderon.CommonSupportMatrixInverse
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

/-- The actual sampled original coefficient has one joint smooth compact support. -/
theorem radiusTwoScaledMetricCoefficient_data (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (fun t : (R3 × ℝ) × R3 =>
      unitBallSmoothCutoff t.2 • principalCoefficient g (t.1.1+t.1.2 • t.2)) ∧
    ∀ (t : R3 × ℝ) (z : R3), z ∉ closedBall (0 : R3) 3 →
      unitBallSmoothCutoff z • principalCoefficient g (t.1+t.2 • z) = 0 := by
  constructor
  · have hPoint : ContDiff ℝ ∞ (fun t : (R3 × ℝ) × R3 => t.1.1+t.1.2 • t.2) :=
      (contDiff_fst.comp contDiff_fst).add ((contDiff_snd.comp contDiff_fst).smul contDiff_snd)
    exact (unitBallSmoothCutoff.contDiff.comp contDiff_snd).smul
      ((contDiff_principalCoefficient g hg).comp hPoint)
  · intro t z hz
    have hDist : (3 : ℝ) ≤ dist z (0 : R3) := by
      change ¬ dist z (0 : R3) ≤ 3 at hz
      exact le_of_lt (lt_of_not_ge hz)
    have hZero := unitBallSmoothCutoff.zero_of_le_dist hDist
    simp only [hZero,zero_smul]

/-- The SAME original closed-radius-two ellipticity constants work for all samples. -/
theorem exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, ∀ (q : R3), q ∈ closedBall (0 : R3) (5/4 : ℝ) →
      ∀ (r : ℝ), 0 ≤ r → r ≤ (1/4 : ℝ) →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z : R3 => unitBallSmoothCutoff z • principalCoefficient g (q+r • z)) lam Lam := by
  obtain ⟨lam,Lam,hEll⟩ := exists_uniformlyEllipticOn_principalCoefficient_closedBall_two g hg
  refine ⟨lam,Lam,?_⟩
  intro q hq r hr hrMax
  refine ⟨hEll.1,hEll.2.1,?_⟩
  intro z hz
  have hqNorm : ‖q‖ ≤ (5/4 : ℝ) := mem_closedBall_zero_iff.mp hq
  have hzNorm : ‖z‖ < (1 : ℝ) := mem_ball_zero_iff.mp hz
  have hSample : q+r • z ∈ closedBall (0 : R3) 2 := by
    apply mem_closedBall_zero_iff.mpr
    calc ‖q+r • z‖ ≤ ‖q‖+‖r • z‖ := norm_add_le _ _
      _ = ‖q‖+r*‖z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
      _ ≤ (5/4 : ℝ)+(1/4 : ℝ) := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hzNorm.le)]
      _ ≤ 2 := by norm_num
  have hChi : unitBallSmoothCutoff z = 1 := unitBallSmoothCutoff_one_of_mem hz
  simpa only [hChi,one_smul] using hEll.2.2 hSample

/-- Uniform native strong inverses for the ACTUAL compact center/radius family. -/
theorem exists_uniform_radiusTwoScaledMetricInverse_apply_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : R3 × ℝ),
      t ∈ (closedBall (0 : R3) (5/4 : ℝ)) ×ˢ Icc (0 : ℝ) (1/4 : ℝ) →
      ∀ f : BallSobolev s,
        ‖(strongDirichletOperator hcalc s
          (commonSupportMatrixFamily (s+2)
            (fun v : (R3 × ℝ) × R3 => unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2))
            (radiusTwoScaledMetricCoefficient_data g hg).1
            (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
            (radiusTwoScaledMetricCoefficient_data g hg).2 t)).inverse f‖ ≤ C*‖f‖ := by
  obtain ⟨lam,Lam,hUE⟩ := exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient g hg
  have hParams : IsCompact ((closedBall (0 : R3) (5/4 : ℝ)) ×ˢ Icc (0 : ℝ) (1/4 : ℝ)) :=
    (isCompact_closedBall (0 : R3) (5/4 : ℝ)).prod isCompact_Icc
  have hEll : ∀ t ∈ (closedBall (0 : R3) (5/4 : ℝ)) ×ˢ Icc (0 : ℝ) (1/4 : ℝ),
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => unitBallSmoothCutoff z • principalCoefficient g (t.1+t.2 • z)) lam Lam := by
    intro t ht
    exact hUE t.1 ht.1 t.2 ht.2.1 ht.2.2
  exact exists_uniform_commonSupportMatrixInverse_apply_bound hcalc hreg s
    (fun v : (R3 × ℝ) × R3 => unitBallSmoothCutoff v.2 • principalCoefficient g (v.1.1+v.1.2 • v.2))
    (radiusTwoScaledMetricCoefficient_data g hg).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (radiusTwoScaledMetricCoefficient_data g hg).2
    ((closedBall (0 : R3) (5/4 : ℝ)) ×ˢ Icc (0 : ℝ) (1/4 : ℝ)) hParams lam Lam hEll

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoScaledMetricCoefficient_data
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniformlyEllipticOn_radiusTwoScaledMetricCoefficient
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniform_radiusTwoScaledMetricInverse_apply_bound
