import Calderon.RadiusTwoSmoothSourceSeparation
import Mathlib.Topology.LocalAtTarget

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace Topology
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

def radiusTwoSourceEvaluationFamily
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) :
    𝓓(fixedExteriorSourceOpens, ℝ) → ℝ :=
  fun f => radiusTwoSmoothSourceResponse hreg hcalc g hg f p

theorem continuous_radiusTwoSourceEvaluationFamily
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (radiusTwoSourceEvaluationFamily hreg hcalc g hg) := by
  apply continuous_pi
  intro f
  exact (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).1

theorem radiusTwoSourceEvaluationFamily_eq_zero_of_norm_ge
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) (hp : 2 ≤ ‖p‖) :
    radiusTwoSourceEvaluationFamily hreg hcalc g hg p = 0 := by
  funext f
  exact (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).2.2.2 p hp

theorem radiusTwoSourceEvaluationFamily_ne_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    radiusTwoSourceEvaluationFamily hreg hcalc g hg p ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_radiusTwoSmoothSourceResponse_ne_zero hreg hcalc hSep g hg p hp
  intro h
  exact hf (congrFun h f)

theorem radiusTwoSourceEvaluationFamily_injective
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Function.Injective (fun p : (radiusTwoOpens : Set R3) =>
      radiusTwoSourceEvaluationFamily hreg hcalc g hg (p : R3)) := by
  intro p q h
  apply radiusTwoSmoothSourceEvaluationLinear_injective hreg hcalc hSep g hg
  ext f
  exact congrFun h f

theorem isEmbedding_radiusTwoSourceEvaluationFamily
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    IsEmbedding (fun p : (radiusTwoOpens : Set R3) =>
      radiusTwoSourceEvaluationFamily hreg hcalc g hg (p : R3)) := by
  let M := closedBall (0 : R3) 2
  letI : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : R3) 2)
  let F := radiusTwoSourceEvaluationFamily hreg hcalc g hg
  let V : Set (𝓓(fixedExteriorSourceOpens, ℝ) → ℝ) := {z | z ≠ 0}
  let FM : M → (𝓓(fixedExteriorSourceOpens, ℝ) → ℝ) := fun x => F x
  have hFM : Continuous FM :=
    (continuous_radiusTwoSourceEvaluationFamily hreg hcalc g hg).comp continuous_subtype_val
  have hInterior (x : M) (hx : FM x ∈ V) : (x : R3) ∈ (radiusTwoOpens : Set R3) := by
    apply mem_ball_zero_iff.mpr
    by_contra h
    exact hx (radiusTwoSourceEvaluationFamily_eq_zero_of_norm_ge hreg hcalc g hg x (le_of_not_gt h))
  let A : Set M := FM ⁻¹' V
  let e : (radiusTwoOpens : Set R3) ≃ₜ A :=
    { toEquiv :=
        { toFun := fun p => ⟨⟨p,ball_subset_closedBall p.property⟩,
            radiusTwoSourceEvaluationFamily_ne_zero hreg hcalc hSep g hg p p.property⟩
          invFun := fun x => ⟨x.val.val,hInterior x.val x.property⟩
          left_inv := by intro p; rfl
          right_inv := by intro x; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hGcont : Continuous (V.restrictPreimage FM) := hFM.restrictPreimage
  have hGinj : Function.Injective (V.restrictPreimage FM) := by
    intro x y h
    have heval : F (e.symm x : R3) = F (e.symm y : R3) := congrArg Subtype.val h
    have hxy := radiusTwoSourceEvaluationFamily_injective hreg hcalc hSep g hg heval
    exact e.symm.injective hxy
  have hG : IsClosedEmbedding (V.restrictPreimage FM) :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap hGcont hGinj (hFM.isClosedMap.restrictPreimage V)
  exact IsEmbedding.subtypeVal.comp (hG.isEmbedding.comp e.isEmbedding)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceEvaluationFamily
#print axioms OAI.AnisotropicCalderon.ExteriorSource.continuous_radiusTwoSourceEvaluationFamily
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceEvaluationFamily_eq_zero_of_norm_ge
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceEvaluationFamily_ne_zero
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceEvaluationFamily_injective
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isEmbedding_radiusTwoSourceEvaluationFamily
