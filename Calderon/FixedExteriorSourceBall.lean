import Calderon.ActualTwoMetricCommonExteriorResponse
import Calderon.MetricVolumeTestEquiv

/-! The full upfront expansion precedes this literal fixed-source geometry. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource

def fixedExteriorSourceCenter : R3 := EuclideanSpace.single (0 : Fin 3) (3/2 : ℝ)

def fixedExteriorSourceOpens : Opens R3 :=
  ⟨ball fixedExteriorSourceCenter (1/8 : ℝ), isOpen_ball⟩

theorem norm_fixedExteriorSourceCenter : ‖fixedExteriorSourceCenter‖ = (3/2 : ℝ) := by
  simp [fixedExteriorSourceCenter, EuclideanSpace.norm_single]

theorem fixedExteriorSource_closedBall_subset_annulus :
    closedBall fixedExteriorSourceCenter (1/8 : ℝ) ⊆
      (exteriorAnnulusOpens : Set R3) := by
  intro x hx
  have hd : ‖x - fixedExteriorSourceCenter‖ ≤ (1/8 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hx
  have hd' : ‖fixedExteriorSourceCenter - x‖ ≤ (1/8 : ℝ) := by
    simpa only [norm_sub_rev] using hd
  have hUpper := norm_le_norm_sub_add x fixedExteriorSourceCenter
  have hLower := norm_le_norm_sub_add fixedExteriorSourceCenter x
  rw [norm_fixedExteriorSourceCenter] at hUpper hLower
  change 1 < ‖x‖ ∧ ‖x‖ < 2
  constructor <;> linarith

theorem fixedExteriorSourceOpens_le_annulus : fixedExteriorSourceOpens ≤ exteriorAnnulusOpens := by
  intro x hx
  exact fixedExteriorSource_closedBall_subset_annulus (ball_subset_closedBall hx)

theorem fixedExteriorSourceOpens_le_radiusTwo : fixedExteriorSourceOpens ≤ radiusTwoOpens :=
  fixedExteriorSourceOpens_le_annulus.trans exteriorAnnulusOpens_le_radiusTwoOpens

theorem fixedExteriorSourceOpens_nonempty : (fixedExteriorSourceOpens : Set R3).Nonempty := by
  exact ⟨fixedExteriorSourceCenter, mem_ball_self (by norm_num : (0 : ℝ) < 1/8)⟩

theorem tsupport_fixedExteriorSourceTest_subset_annulus
    (φ : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    tsupport φ ⊆ (exteriorAnnulusOpens : Set R3) :=
  φ.tsupport_subset.trans fixedExteriorSourceOpens_le_annulus

theorem metricVolumeTestMap_fixedExteriorSource
    (g : MatrixField) (hg : IsAdmissibleMetric g) (φ : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    metricVolumeTestMap g hg fixedExteriorSourceOpens φ = φ := by
  apply metricVolumeTestMap_eq_self_of_tsupport_exterior
  intro x hx
  exact (tsupport_fixedExteriorSourceTest_subset_annulus φ hx).1.le

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceCenter
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_fixedExteriorSourceCenter
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSource_closedBall_subset_annulus
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceOpens_le_annulus
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceOpens_le_radiusTwo
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fixedExteriorSourceOpens_nonempty
#print axioms OAI.AnisotropicCalderon.ExteriorSource.tsupport_fixedExteriorSourceTest_subset_annulus
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestMap_fixedExteriorSource
