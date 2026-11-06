import Calderon.RadiusTwoNativeSourceFoundation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-! EXPANSION.json precedes actual polynomial barrier native construction and jets. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal Distributions Gradient Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

def radiusThreeOpens : Opens R3 := ⟨ball (0 : R3) 3,isOpen_ball⟩

lemma radiusTwoOpens_le_radiusThreeOpens : radiusTwoOpens ≤ radiusThreeOpens := by
  intro x hx
  change x ∈ ball (0 : R3) 2 at hx
  change x ∈ ball (0 : R3) 3
  exact ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) hx

def radiusTwoBarrierBump : ContDiffBump (0 : R3) :=
  ⟨(9/4 : ℝ),(5/2 : ℝ),by norm_num,by norm_num⟩

def radiusTwoBarrierTest (M : ℝ) : 𝓓(radiusThreeOpens, ℝ) where
  toFun x := radiusTwoBarrierBump x * (M*(4-‖x‖^2))
  contDiff' := radiusTwoBarrierBump.contDiff.mul
    (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))
  hasCompactSupport' := radiusTwoBarrierBump.hasCompactSupport.mul_right
  tsupport_subset' := by
    intro x hx
    have hBump : x ∈ tsupport (radiusTwoBarrierBump : R3 → ℝ) :=
      tsupport_mul_subset_left hx
    rw [ContDiffBump.tsupport_eq] at hBump
    have hNorm : ‖x‖ ≤ (5/2 : ℝ) := by
      simpa only [mem_closedBall,dist_zero_right,radiusTwoBarrierBump] using hBump
    change x ∈ ball (0 : R3) 3
    exact mem_ball_zero_iff.mpr (hNorm.trans_lt (by norm_num))

def radiusTwoBarrierH1 (M : ℝ) : RadiusTwoH1 :=
  TauCeti.W1p.restrictL radiusTwoOpens_le_radiusThreeOpens
    (TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) radiusThreeOpens 2 (radiusTwoBarrierTest M))

lemma gradient_radiusTwoBarrierPolynomial (M : ℝ) (x : R3) :
    ∇ (fun y : R3 => M*(4-‖y‖^2)) x = (-2*M) • x := by
  have hD : HasFDerivAt (fun y : R3 => M*(4-‖y‖^2))
      ((InnerProductSpace.toDual ℝ R3) ((-2*M) • x)) x := by
    convert ((hasFDerivAt_const (4 : ℝ) x).sub
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul M using 1
    ext y
    simp only [InnerProductSpace.toDual_apply_apply,real_inner_smul_left,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply,innerSL_apply_apply,smul_eq_mul]
    ring
  exact (hasGradientAt_iff_hasFDerivAt.mpr hD).gradient

lemma radiusTwoBarrierH1_value_ae (M : ℝ) :
    ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      TauCeti.W1p.value (radiusTwoBarrierH1 M) x = M*(4-‖x‖^2) := by
  have hMu : (volume : Measure R3).restrict radiusTwoOpens ≤
      (volume : Measure R3).restrict radiusThreeOpens :=
    Measure.restrict_mono_set volume (SetLike.coe_subset_coe.mpr radiusTwoOpens_le_radiusThreeOpens)
  have hTest := (TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
    (radiusTwoBarrierTest M)).filter_mono (ae_mono hMu)
  filter_upwards [TauCeti.W1p.value_restrictL_ae radiusTwoOpens_le_radiusThreeOpens
      (TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) radiusThreeOpens 2 (radiusTwoBarrierTest M)),
    hTest,ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hRestr hPhi hx
  have hNorm : ‖x‖ < 2 := by
    change x ∈ ball (0 : R3) 2 at hx
    exact mem_ball_zero_iff.mp hx
  have hOne : radiusTwoBarrierBump x = 1 := radiusTwoBarrierBump.one_of_mem_closedBall
    (mem_closedBall_zero_iff.mpr (hNorm.le.trans (by norm_num [radiusTwoBarrierBump])))
  change TauCeti.W1p.value (TauCeti.W1p.restrictL radiusTwoOpens_le_radiusThreeOpens _) x = _
  rw [hRestr,TauCeti.W1p.value_ofTestFunctionₗ,hPhi]
  change radiusTwoBarrierBump x * (M*(4-‖x‖^2)) = _
  rw [hOne,one_mul]

lemma radiusTwoBarrierH1_gradient_ae (M : ℝ) :
    ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      TauCeti.W1p.gradient (radiusTwoBarrierH1 M) x = (-2*M) • x := by
  have hMu : (volume : Measure R3).restrict radiusTwoOpens ≤
      (volume : Measure R3).restrict radiusThreeOpens :=
    Measure.restrict_mono_set volume (SetLike.coe_subset_coe.mpr radiusTwoOpens_le_radiusThreeOpens)
  have hTest := (TauCeti.gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
    (radiusTwoBarrierTest M)).filter_mono (ae_mono hMu)
  filter_upwards [TauCeti.W1p.gradient_restrictL_ae radiusTwoOpens_le_radiusThreeOpens
      (TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) radiusThreeOpens 2 (radiusTwoBarrierTest M)),
    hTest,ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hRestr hPhi hx
  have hNorm : ‖x‖ < 2 := by
    change x ∈ ball (0 : R3) 2 at hx
    exact mem_ball_zero_iff.mp hx
  have hNear := radiusTwoBarrierBump.eventuallyEq_one_of_mem_ball
    (mem_ball_zero_iff.mpr (hNorm.trans_le (by norm_num [radiusTwoBarrierBump])))
  have hEqual : (radiusTwoBarrierTest M : R3 → ℝ) =ᶠ[𝓝 x]
      (fun y : R3 => M*(4-‖y‖^2)) := by
    filter_upwards [hNear] with y hy
    change radiusTwoBarrierBump y * (M*(4-‖y‖^2)) = _
    rw [hy,Pi.one_apply,one_mul]
  change TauCeti.W1p.gradient (TauCeti.W1p.restrictL radiusTwoOpens_le_radiusThreeOpens _) x = _
  rw [hRestr,TauCeti.W1p.gradient_ofTestFunctionₗ,hPhi,hEqual.gradient_eq,
    gradient_radiusTwoBarrierPolynomial]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusThreeOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoOpens_le_radiusThreeOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrierBump
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrierTest
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrierH1
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.gradient_radiusTwoBarrierPolynomial
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrierH1_value_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrierH1_gradient_ae
