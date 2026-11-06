import Calderon.ActualEnlargedBallNormalizedMetric
import Calderon.TauMetricCoercivity
import Calderon.SmoothSobolevBridge

/-! EXPANSION.json precedes the literal radius-two native source domain/coercivity foundation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

def radiusTwoOpens : Opens R3 := ⟨ball (0 : R3) 2,isOpen_ball⟩
abbrev RadiusTwoH1 := TauCeti.W1p (volume : Measure R3) radiusTwoOpens 2
abbrev RadiusTwoH1Zero := TauCeti.W1p0 (volume : Measure R3) radiusTwoOpens 2
abbrev RadiusTwoL2 := Lp ℝ 2 ((volume : Measure R3).restrict radiusTwoOpens)

theorem ballOpens_le_radiusTwoOpens : ballOpens ≤ radiusTwoOpens := by
  intro x hx
  have h : x ∈ ball (0 : R3) (1 : ℝ) := hx
  exact ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) h

theorem isAdmissibleMetric_radiusTwoNormalized
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    IsAdmissibleMetric (enlargedBallNormalizedMetric g 2) :=
  isAdmissibleMetric_enlargedBallNormalizedMetric g hg 2 (by norm_num)

theorem principalCoefficient_radiusTwoNormalized_half
    (g : MatrixField) (x : R3) :
    principalCoefficient (enlargedBallNormalizedMetric g 2) ((1/2 : ℝ) • x) =
      principalCoefficient g x := by
  rw [principalCoefficient_enlargedBallNormalizedMetric,smul_smul]
  norm_num

theorem half_smul_mem_closedBall_one_of_mem_closedBall_two
    (x : R3) (hx : x ∈ closedBall (0 : R3) 2) :
    (1/2 : ℝ) • x ∈ closedBall (0 : R3) 1 := by
  have hnorm : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
  rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
  norm_num
  linarith

theorem exists_uniformlyEllipticOn_principalCoefficient_closedBall_two
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 2)
      (principalCoefficient g) lam Lam := by
  obtain ⟨lam,Lam,hu⟩ := exists_uniformlyEllipticOn_principalCoefficient
    (enlargedBallNormalizedMetric g 2) (isAdmissibleMetric_radiusTwoNormalized g hg)
  refine ⟨lam,Lam,hu.1,hu.2.1,?_⟩
  intro x hx
  have hy := half_smul_mem_closedBall_one_of_mem_closedBall_two x hx
  have hBounds := hu.2.2 hy
  rw [principalCoefficient_radiusTwoNormalized_half] at hBounds
  exact hBounds

theorem exists_uniformlyEllipticOn_principalCoefficient_radiusTwo
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (radiusTwoOpens : Set R3)
      (principalCoefficient g) lam Lam := by
  obtain ⟨lam,Lam,hu⟩ := exists_uniformlyEllipticOn_principalCoefficient_closedBall_two g hg
  exact ⟨lam,Lam,hu.mono_set ball_subset_closedBall⟩

theorem memLp_radiusTwoMetricEnergyIntegrand
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict radiusTwoOpens) := by
  obtain ⟨lam,Lam,hu⟩ := exists_uniformlyEllipticOn_principalCoefficient_radiusTwo g hg
  exact TauCeti.PDE.memLp_energyIntegrand_of_bounds hu.upper_nonneg
    (continuous_principalCoefficient g hg).aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx eta xi => hu.upper_bound hx eta xi)
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

theorem isCoercive_radiusTwoMetricEnergy
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    IsCoercive (TauCeti.PDE.energyFormH1L0
      (mu := (volume : Measure R3)) (Omega := radiusTwoOpens)
      (a := principalCoefficient g) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
      (memLp_radiusTwoMetricEnergyIntegrand g hg)) := by
  obtain ⟨lam,Lam,hu⟩ := exists_uniformlyEllipticOn_principalCoefficient_radiusTwo g hg
  apply TauCeti.PDE.isCoercive_energyFormH1L0 (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (C := lam^2 / (2*lam*((2*(2 : ℝ))^2+1)))
  · have hlam : 0 < lam := hu.pos
    positivity
  · intro w
    have hn : ‖(w : RadiusTwoH1)‖ = ‖w‖ := rfl
    have hb := hu.mul_norm_sq_le_energyFormH1_self_of_subset_ball
      (continuous_principalCoefficient g hg).aestronglyMeasurable
      aestronglyMeasurable_const aestronglyMeasurable_const
      (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (beta := 0) (gamma := 0)
      (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
      (z := 0) (R := 2)
      (show (radiusTwoOpens : Set R3) ⊆ ball (0 : R3) 2 from Set.Subset.rfl) w.2
    rw [hn] at hb
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul,sub_zero,mul_one] using hb

theorem memLp_two_radiusTwo_of_continuous
    (f : R3 → ℝ) (hf : Continuous f) :
    MemLp f 2 ((volume : Measure R3).restrict radiusTwoOpens) := by
  have hB : MeasurableSet (radiusTwoOpens : Set R3) := isOpen_ball.measurableSet
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict radiusTwoOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,radiusTwoOpens,Opens.coe_mk] using
      ((measure_mono (show ball (0 : R3) 2 ⊆ closedBall (0 : R3) 2 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 2).measure_lt_top)⟩
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : R3) 2).bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hB] with x hx
  exact hC ⟨x,ball_subset_closedBall hx,rfl⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.ballOpens_le_radiusTwoOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isAdmissibleMetric_radiusTwoNormalized
#print axioms OAI.AnisotropicCalderon.ExteriorSource.principalCoefficient_radiusTwoNormalized_half
#print axioms OAI.AnisotropicCalderon.ExteriorSource.half_smul_mem_closedBall_one_of_mem_closedBall_two
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniformlyEllipticOn_principalCoefficient_closedBall_two
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_uniformlyEllipticOn_principalCoefficient_radiusTwo
#print axioms OAI.AnisotropicCalderon.ExteriorSource.memLp_radiusTwoMetricEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isCoercive_radiusTwoMetricEnergy
#print axioms OAI.AnisotropicCalderon.ExteriorSource.memLp_two_radiusTwo_of_continuous
