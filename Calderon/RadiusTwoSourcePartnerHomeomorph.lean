import Calderon.RadiusTwoSourcePointwiseEmbedding
import Calderon.RadiusTwoSmoothSourceCommonExterior
import Mathlib.Topology.Homeomorph.Lemmas

/-! Full upfront expansion precedes this downstream PROJECT implication.
hImage is the explicitly still-open novel image-equality obligation. It is not
a literature premise, is not adopted here and is not added to Main. The codomain
of each source family has the literal product/pointwise topology. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace Topology
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

variable (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
variable (hSep : RadiusTwoSourceSeparation)
variable (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
/- The remaining NOVEL project image-equality hypothesis, not an analytic interface. -/
variable (hImage :
  Set.range (fun p : (radiusTwoOpens : Set R3) =>
    radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁ (p : R3)) =
  Set.range (fun q : (radiusTwoOpens : Set R3) =>
    radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂ (q : R3)))

/-- Partner map from metric one's interior to metric two's interior, conditional
on the still-open equality of the two actual source-evaluation images. -/
def radiusTwoSourcePartnerHomeomorph :
    (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3) :=
  (((isEmbedding_radiusTwoSourceEvaluationFamily hreg hcalc hSep g₁ hg₁).toHomeomorph).trans
    (Homeomorph.setCongr hImage)).trans
      ((isEmbedding_radiusTwoSourceEvaluationFamily hreg hcalc hSep g₂ hg₂).toHomeomorph).symm

theorem radiusTwoSourcePartnerHomeomorph_family
    (p : (radiusTwoOpens : Set R3)) :
    radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂
        (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p : R3) =
      radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁ (p : R3) := by
  let e₁ := (isEmbedding_radiusTwoSourceEvaluationFamily hreg hcalc hSep g₁ hg₁).toHomeomorph
  let e₂ := (isEmbedding_radiusTwoSourceEvaluationFamily hreg hcalc hSep g₂ hg₂).toHomeomorph
  have h := congrArg Subtype.val (e₂.apply_symm_apply (Homeomorph.setCongr hImage (e₁ p)))
  change radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂
        (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p : R3) =
      radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁ (p : R3) at h
  exact h

theorem radiusTwoSourcePartnerHomeomorph_response
    (p : (radiusTwoOpens : Set R3)) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSmoothSourceResponse hreg hcalc g₂ hg₂ f
        (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p : R3) =
      radiusTwoSmoothSourceResponse hreg hcalc g₁ hg₁ f (p : R3) :=
  congrFun (radiusTwoSourcePartnerHomeomorph_family hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p) f

theorem radiusTwoSourcePartnerHomeomorph_eq_of_family
    (p q : (radiusTwoOpens : Set R3))
    (hq : radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂ (q : R3) =
      radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁ (p : R3)) :
    radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p = q := by
  apply radiusTwoSourceEvaluationFamily_injective hreg hcalc hSep g₂ hg₂
  exact (radiusTwoSourcePartnerHomeomorph_family hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p).trans hq.symm

theorem radiusTwoSourcePartnerHomeomorph_unique
    (Ψ : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3))
    (hΨ : ∀ p : (radiusTwoOpens : Set R3),
      radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂ (Ψ p : R3) =
        radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁ (p : R3)) :
    Ψ = radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage := by
  apply Homeomorph.ext
  intro p
  exact (radiusTwoSourcePartnerHomeomorph_eq_of_family hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage
    p (Ψ p) (hΨ p)).symm

theorem radiusTwoSourcePartnerHomeomorph_symm_family
    (q : (radiusTwoOpens : Set R3)) :
    radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁
        ((radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage).symm q : R3) =
      radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂ (q : R3) := by
  have h := radiusTwoSourcePartnerHomeomorph_family hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage
    ((radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage).symm q)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

theorem radiusTwoSourcePartnerHomeomorph_symm_response
    (q : (radiusTwoOpens : Set R3)) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSmoothSourceResponse hreg hcalc g₁ hg₁ f
        ((radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage).symm q : R3) =
      radiusTwoSmoothSourceResponse hreg hcalc g₂ hg₂ f (q : R3) :=
  congrFun (radiusTwoSourcePartnerHomeomorph_symm_family hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage q) f

theorem continuous_radiusTwoSourcePartnerHomeomorph :
    Continuous (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage) :=
  (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage).continuous

theorem continuous_radiusTwoSourcePartnerHomeomorph_symm :
    Continuous (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage).symm :=
  (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage).continuous_symm

/-- The original all-smooth energy equality fixes every actual exterior pole;
it is not used to presume the still-open equality hImage. -/
theorem radiusTwoSourcePartnerHomeomorph_eq_self_of_exterior
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (p : (radiusTwoOpens : Set R3)) (hp : (p : R3) ∈ (exteriorAnnulusOpens : Set R3)) :
    radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p = p := by
  apply radiusTwoSourcePartnerHomeomorph_eq_of_family hreg hcalc hSep g₁ g₂ hg₁ hg₂ hImage p p
  exact (radiusTwoSmoothSourceResponse_exterior_family_eq hreg hcalc g₁ g₂ hg₁ hg₂ hΛ p hp).symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_family
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_response
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_eq_of_family
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_unique
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_symm_family
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_symm_response
#print axioms OAI.AnisotropicCalderon.ExteriorSource.continuous_radiusTwoSourcePartnerHomeomorph
#print axioms OAI.AnisotropicCalderon.ExteriorSource.continuous_radiusTwoSourcePartnerHomeomorph_symm
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourcePartnerHomeomorph_eq_self_of_exterior
