import Calderon.NativePrincipalSmoothFluxDictionary
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.TestFunction
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Distributions
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume

def parametrixInteriorCutoff : ContDiffBump (0 : R3) :=
  ⟨1/4,1/2,by norm_num,by norm_num⟩

def parametrixCollarFactor (z : R3) : ℝ := 1-parametrixInteriorCutoff z

theorem contDiff_parametrixCollarFactor : ContDiff ℝ ∞ parametrixCollarFactor := by
  exact contDiff_const.sub parametrixInteriorCutoff.contDiff

theorem parametrixCollarFactor_zero_of_mem_ball (z : R3)
    (hz : z ∈ ball (0 : R3) (1/4)) : parametrixCollarFactor z = 0 := by
  unfold parametrixCollarFactor
  rw [parametrixInteriorCutoff.one_of_mem_closedBall (ball_subset_closedBall hz),sub_self]

theorem parametrixCollarFactor_one_of_notMem_closedBall (z : R3)
    (hz : z ∉ closedBall (0 : R3) (1/2)) : parametrixCollarFactor z = 1 := by
  have h : (1/2 : ℝ) ≤ dist z 0 := (not_le.mp hz).le
  unfold parametrixCollarFactor
  rw [parametrixInteriorCutoff.zero_of_le_dist h,sub_zero]

def parametrixBoundaryInteriorCutoff : ContDiffBump (0 : R3) :=
  ⟨2/3,3/4,by norm_num,by norm_num⟩

def parametrixBoundaryCutoff (z : R3) : ℝ := 1-parametrixBoundaryInteriorCutoff z

theorem contDiff_parametrixBoundaryCutoff : ContDiff ℝ ∞ parametrixBoundaryCutoff := by
  exact contDiff_const.sub parametrixBoundaryInteriorCutoff.contDiff

theorem parametrixBoundaryCutoff_zero_of_mem_closedBall (z : R3)
    (hz : z ∈ closedBall (0 : R3) (1/2)) : parametrixBoundaryCutoff z = 0 := by
  have h : z ∈ closedBall (0 : R3) parametrixBoundaryInteriorCutoff.rIn := by
    apply mem_closedBall_zero_iff.mpr
    have hnorm := mem_closedBall_zero_iff.mp hz
    change ‖z‖ ≤ (2/3 : ℝ)
    linarith
  unfold parametrixBoundaryCutoff
  rw [parametrixBoundaryInteriorCutoff.one_of_mem_closedBall h,sub_self]

theorem parametrixBoundaryCutoff_one_of_mem_sphere (z : R3)
    (hz : z ∈ sphere (0 : R3) 1) : parametrixBoundaryCutoff z = 1 := by
  have h : parametrixBoundaryInteriorCutoff.rOut ≤ dist z 0 := by
    rw [dist_zero_right,mem_sphere_zero_iff_norm.mp hz]
    norm_num [parametrixBoundaryInteriorCutoff]
  unfold parametrixBoundaryCutoff
  rw [parametrixBoundaryInteriorCutoff.zero_of_le_dist h,sub_zero]

def parametrixTestCutoff : ContDiffBump (0 : R3) :=
  ⟨3/5,4/5,by norm_num,by norm_num⟩

theorem parametrixTestCutoff_tsupport_subset :
    tsupport (parametrixTestCutoff : R3 → ℝ) ⊆ (ballOpens : Set R3) := by
  rw [parametrixTestCutoff.tsupport_eq]
  intro z hz
  change z ∈ ball (0 : R3) 1
  apply mem_ball_zero_iff.mpr
  have hnorm := mem_closedBall_zero_iff.mp hz
  change ‖z‖ ≤ (4/5 : ℝ) at hnorm
  linarith

theorem parametrixTestCutoff_eventuallyEq_one (z : R3)
    (hz : z ∈ closedBall (0 : R3) (1/2)) :
    (parametrixTestCutoff : R3 → ℝ) =ᶠ[𝓝 z] (fun _ => 1) := by
  apply parametrixTestCutoff.eventuallyEq_one_of_mem_ball
  apply mem_ball_zero_iff.mpr
  have hnorm := mem_closedBall_zero_iff.mp hz
  change ‖z‖ < (3/5 : ℝ)
  linarith

theorem parametrixTestCutoff_zero : parametrixTestCutoff (0 : R3) = 1 := by
  exact parametrixTestCutoff.eventuallyEq_one.eq_of_nhds

def parametrixHarmonicTest (u : SmoothData) : 𝓓(ballOpens, ℝ) :=
  ⟨fun z => parametrixTestCutoff z * u.1 z,
    parametrixTestCutoff.contDiff.mul u.2,
    parametrixTestCutoff.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans parametrixTestCutoff_tsupport_subset⟩

theorem parametrixHarmonicTest_apply (u : SmoothData) (z : R3) :
    parametrixHarmonicTest u z = parametrixTestCutoff z * u.1 z := by
  rfl

theorem parametrixHarmonicTest_eventuallyEq (u : SmoothData) (z : R3)
    (hz : z ∈ closedBall (0 : R3) (1/2)) :
    (parametrixHarmonicTest u : R3 → ℝ) =ᶠ[𝓝 z] u.1 := by
  filter_upwards [parametrixTestCutoff_eventuallyEq_one z hz] with x hx
  change parametrixTestCutoff x * u.1 x = u.1 x
  rw [hx,one_mul]

theorem parametrixHarmonicTest_eq (u : SmoothData) (z : R3)
    (hz : z ∈ closedBall (0 : R3) (1/2)) : parametrixHarmonicTest u z = u.1 z := by
  exact (parametrixHarmonicTest_eventuallyEq u z hz).eq_of_nhds

theorem parametrixHarmonicTest_zero (u : SmoothData) :
    parametrixHarmonicTest u (0 : R3) = u.1 0 := by
  exact parametrixHarmonicTest_eq u 0 (by simp)

theorem coordinateFluxDivergence_parametrixHarmonicTest_eq
    (a : MatrixField) (u : SmoothData) (z : R3)
    (hz : z ∈ closedBall (0 : R3) (1/2)) :
    coordinateFluxDivergence
      (fun x => matrixOperatorMap (a x) (gradient (parametrixHarmonicTest u) x)) z =
    coordinateFluxDivergence
      (fun x => matrixOperatorMap (a x) (gradient u.1 x)) z := by
  exact coordinateFluxDivergence_matrixGradient_congr_of_eventuallyEq a _ _ z
    (parametrixHarmonicTest_eventuallyEq u z hz)


theorem parametrixHarmonicTest_tsupport_subset_closedBall (u : SmoothData) :
    tsupport (parametrixHarmonicTest u : R3 → ℝ) ⊆ closedBall (0 : R3) (4/5) := by
  change tsupport (fun z => parametrixTestCutoff z * u.1 z) ⊆ _
  exact tsupport_mul_subset_left.trans (by rw [parametrixTestCutoff.tsupport_eq]; rfl)

theorem parametrixHarmonicTest_commonCompactSupport :
    ∃ K : Set R3, IsCompact K ∧ K ⊆ (ballOpens : Set R3) ∧
      ∀ u : SmoothData, tsupport (parametrixHarmonicTest u : R3 → ℝ) ⊆ K := by
  refine ⟨closedBall (0 : R3) (4/5),isCompact_closedBall _ _,?_,parametrixHarmonicTest_tsupport_subset_closedBall⟩
  change closedBall (0 : R3) parametrixTestCutoff.rOut ⊆ _
  rw [← parametrixTestCutoff.tsupport_eq]
  exact parametrixTestCutoff_tsupport_subset

end OAI.AnisotropicCalderon.ConnectionError
