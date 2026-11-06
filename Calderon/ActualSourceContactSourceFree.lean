import Calderon.ActualCommonSourceContact
import Calderon.RadiusTwoSmoothSourceCommonExterior

set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped ContDiff Topology Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

lemma norm_le_one_of_radiusTwoSourceEvaluationFamily_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ (∞ : ℕ∞ω) f → minimalEnergy g1 f = minimalEnergy g2 f)
    (x q : R3) (hxB : x ∈ (radiusTwoOpens : Set R3))
    (hqB : q ∈ (radiusTwoOpens : Set R3)) (hx : ‖x‖ ≤ 1)
    (hContact : radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 q =
      radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x) : ‖q‖ ≤ 1 := by
  classical
  by_contra h
  have hBig : 1 < ‖q‖ := lt_of_not_ge h
  have hAnnulus : q ∈ (exteriorAnnulusOpens : Set R3) := by
    change 1 < ‖q‖ ∧ ‖q‖ < 2
    exact ⟨hBig,mem_ball_zero_iff.mp hqB⟩
  have hExterior : radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 q =
      radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 q :=
    radiusTwoSmoothSourceResponse_exterior_family_eq hreg hcalc g1 g2 hg1 hg2 hΛ q hAnnulus
  have hEqual : radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 q =
      radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x := hExterior.symm.trans hContact
  have hPoints : (⟨q,hqB⟩ : (radiusTwoOpens : Set R3)) = ⟨x,hxB⟩ := by
    apply radiusTwoSourceEvaluationFamily_injective hreg hcalc hSep g2 hg2
    exact hEqual
  have hqx : q = x := congrArg Subtype.val hPoints
  rw [hqx] at hBig
  exact (not_lt_of_ge hx) hBig

lemma notMem_fixedExteriorSource_closedBall_of_norm_le_one
    (x : R3) (hx : ‖x‖ ≤ 1) :
    x ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) := by
  intro hSource
  have hAnnulus := fixedExteriorSource_closedBall_subset_annulus hSource
  change 1 < ‖x‖ ∧ ‖x‖ < 2 at hAnnulus
  exact (not_lt_of_ge hx) hAnnulus.1

theorem exists_radiusTwoSource_sourceFree_contact_and_tendsto
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ (∞ : ℕ∞ω) f → minimalEnergy g1 f = minimalEnergy g2 f)
    (W : Set R3) (Psi : W → (radiusTwoOpens : Set R3))
    (hMatch : ∀ x : W,
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Psi x : R3) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (x : R3))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) (hpW : p ∈ closure W)
    (hpUnit : ‖p‖ ≤ 1) :
    ∃ q : (radiusTwoOpens : Set R3),
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (q : R3) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 p ∧
      Tendsto Psi (Filter.comap (Subtype.val : W → R3) (𝓝 p)) (𝓝 q) ∧
      ‖(q : R3)‖ ≤ 1 ∧
      (q : R3) ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
      p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) := by
  obtain ⟨q,hContact,hTendsto⟩ := exists_radiusTwoSource_contact_and_tendsto
    hreg hcalc hSep g1 g2 hg1 hg2 W Psi hMatch p hp hpW
  have hqUnit := norm_le_one_of_radiusTwoSourceEvaluationFamily_eq
    hreg hcalc hSep g1 g2 hg1 hg2 hΛ p q hp q.property hpUnit hContact
  exact ⟨q,hContact,hTendsto,hqUnit,
    notMem_fixedExteriorSource_closedBall_of_norm_le_one q hqUnit,
    notMem_fixedExteriorSource_closedBall_of_norm_le_one p hpUnit⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_le_one_of_radiusTwoSourceEvaluationFamily_eq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.notMem_fixedExteriorSource_closedBall_of_norm_le_one
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSource_sourceFree_contact_and_tendsto
