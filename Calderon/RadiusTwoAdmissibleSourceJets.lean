import Calderon.RadiusTwoSmoothSourceJetLinear
import Calderon.RadiusTwoSmoothSourceClassicalEquation

/-! The actual symmetric PDE-compatible range inclusion. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume Literature

def radiusTwoRawJetFunctional (g : MatrixField) (p : R3) : RadiusTwoRawTwoJet →ₗ[ℝ] ℝ where
  toFun j := nativeMetricJetFunctional g p j.2.1 j.2.2
  map_add' j k := by
    simp only [nativeMetricJetFunctional, Prod.snd_add, Prod.fst_add,
      ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
    ring
  map_smul' c j := by
    change nativeMetricJetFunctional g p (c • j.2.1) (c • j.2.2) =
      c * nativeMetricJetFunctional g p j.2.1 j.2.2
    simp only [nativeMetricJetFunctional,
      ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Fin.sum_univ_succ, Finset.sum_empty, add_zero]
    ring

def radiusTwoSymmetricRawJets : Submodule ℝ RadiusTwoRawTwoJet where
  carrier := {j | ∀ v w : R3, j.2.2 v w = j.2.2 w v}
  zero_mem' := by intro v w; rfl
  add_mem' := by
    intro j k hj hk v w
    change (j.2.2 + k.2.2) v w = (j.2.2 + k.2.2) w v
    simp only [ContinuousLinearMap.add_apply]
    rw [hj v w,hk v w]
  smul_mem' := by
    intro c j hj v w
    change (c • j.2.2) v w = (c • j.2.2) w v
    simp only [ContinuousLinearMap.smul_apply]
    rw [hj v w]

def radiusTwoAdmissibleRawJets (g : MatrixField) (p : R3) : Submodule ℝ RadiusTwoRawTwoJet :=
  radiusTwoSymmetricRawJets ⊓ LinearMap.ker (radiusTwoRawJetFunctional g p)

theorem range_radiusTwoSmoothSourceJetLinear_le_admissible
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hOutside : p ∉ (fixedExteriorSourceOpens : Set R3)) :
    LinearMap.range (radiusTwoSmoothSourceJetLinear hreg hcalc g hg p hp) ≤
      radiusTwoAdmissibleRawJets g p := by
  intro j hj
  obtain ⟨φ,rfl⟩ := hj
  constructor
  · intro v w
    exact radiusTwoSmoothSourceResponse_second_derivative_symmetric hreg hcalc g hg φ p hp v w
  · change nativeMetricJetFunctional g p
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ) p)
      (fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg φ)) p) = 0
    exact nativeMetricJetFunctional_radiusTwoSmoothSourceResponse_eq_zero
      hreg hcalc g hg φ p hp hOutside

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoRawJetFunctional
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSymmetricRawJets
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoAdmissibleRawJets
#print axioms OAI.AnisotropicCalderon.ExteriorSource.range_radiusTwoSmoothSourceJetLinear_le_admissible
