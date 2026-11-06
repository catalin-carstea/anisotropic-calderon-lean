import Calderon.RadiusTwoSourcePartnerHomeomorph
import Calderon.RadiusTwoSourceCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

theorem contDiffAt_radiusTwoSource_family_partner_of_continuous
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (Psi : ↥(radiusTwoOpens : Set R3) → ↥(radiusTwoOpens : Set R3))
    (hPsi : Continuous Psi)
    (hMatch : ∀ p : (radiusTwoOpens : Set R3),
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Psi p : R3) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (p : R3))
    (F : R3 → R3)
    (hValue : ∀ x (hx : x ∈ (radiusTwoOpens : Set R3)), F x = (Psi ⟨x,hx⟩ : R3)) :
    ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ F x := by
  classical
  have hAcont : ContinuousOn F (radiusTwoOpens : Set R3) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hFun : (radiusTwoOpens : Set R3).domRestrict F =
        (fun p : (radiusTwoOpens : Set R3) => (Psi p : R3)) := by
      funext p
      exact hValue p p.property
    rw [hFun]
    exact continuous_subtype_val.comp hPsi
  intro x hx
  let q : (radiusTwoOpens : Set R3) := Psi ⟨x,hx⟩
  obtain ⟨f,e,he,hq,hInverse⟩ := exists_radiusTwoSourceCoordinates_localChart
    hreg hcalc hSep g1 hg1 q q.property
  let F2 : R3 → (Fin 3 → ℝ) := radiusTwoSourceCoordinates hreg hcalc g2 hg2 f
  have hValues (p : (radiusTwoOpens : Set R3)) : F2 p = e (Psi p : R3) := by
    rw [he]
    funext i
    exact (congrFun (hMatch p) (f i)).symm
  have hBase : F2 x = e (q : R3) := hValues ⟨x,hx⟩
  have hF2 : ContDiffAt ℝ ∞ F2 x :=
    (contDiffOn_radiusTwoSourceCoordinates hreg hcalc g2 hg2 f).contDiffAt
      (radiusTwoOpens.isOpen.mem_nhds hx)
  have hInverse' : ContDiffAt ℝ ∞ e.symm (F2 x) := by
    rw [hBase]
    exact hInverse
  have hComp : ContDiffAt ℝ ∞ (fun y : R3 => e.symm (F2 y)) x :=
    hInverse'.comp x hF2
  have hAx : F x = (q : R3) := hValue x hx
  have hAat : ContinuousAt F x :=
    hAcont.continuousAt (radiusTwoOpens.isOpen.mem_nhds hx)
  have hNear : ∀ᶠ y in 𝓝 x, F y ∈ e.source := by
    apply hAat
    rw [hAx]
    exact e.open_source.mem_nhds hq
  have hEq : F =ᶠ[𝓝 x] (fun y : R3 => e.symm (F2 y)) := by
    filter_upwards [radiusTwoOpens.isOpen.mem_nhds hx,hNear] with y hy hye
    have hyA : F y = (Psi ⟨y,hy⟩ : R3) := hValue y hy
    have hV : F2 y = e (F y) := by
      rw [hyA]
      exact hValues ⟨y,hy⟩
    rw [hV]
    exact (e.left_inv hye).symm
  exact hComp.congr_of_eventuallyEq hEq

theorem contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hImage :
      Set.range (fun p : (radiusTwoOpens : Set R3) =>
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (p : R3)) =
      Set.range (fun q : (radiusTwoOpens : Set R3) =>
        radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (q : R3)))
    (F : R3 → R3)
    (hValue : ∀ x (hx : x ∈ (radiusTwoOpens : Set R3)),
      F x = (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage
        ⟨x,hx⟩ : R3)) :
    ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ F x := by
  exact contDiffAt_radiusTwoSource_family_partner_of_continuous
    hreg hcalc hSep g1 g2 hg1 hg2
    (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage)
    (continuous_radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage)
    (radiusTwoSourcePartnerHomeomorph_family hreg hcalc hSep g2 g1 hg2 hg1 hImage) F hValue

theorem contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped_symm
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hImage :
      Set.range (fun p : (radiusTwoOpens : Set R3) =>
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (p : R3)) =
      Set.range (fun q : (radiusTwoOpens : Set R3) =>
        radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (q : R3)))
    (F : R3 → R3)
    (hValue : ∀ x (hx : x ∈ (radiusTwoOpens : Set R3)),
      F x = ((radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage).symm
        ⟨x,hx⟩ : R3)) :
    ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ F x := by
  exact contDiffAt_radiusTwoSource_family_partner_of_continuous
    hreg hcalc hSep g2 g1 hg2 hg1
    (radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage).symm
    (continuous_radiusTwoSourcePartnerHomeomorph_symm hreg hcalc hSep g2 g1 hg2 hg1 hImage)
    (radiusTwoSourcePartnerHomeomorph_symm_family hreg hcalc hSep g2 g1 hg2 hg1 hImage) F hValue

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffAt_radiusTwoSource_family_partner_of_continuous
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped_symm
