import Calderon.RadiusTwoSmoothSourceResponse
import Calderon.FiniteDimensionalJetRange
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Full upfront expansion precedes these actual raw source jets. The response is
smooth only on the open radius-two ball. Second-derivative linearity is obtained
from equality of first-derivative GERMS there. The raw target includes arbitrary
bilinear maps; its PDE kernel alone is not the symmetric admissible jet space. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

abbrev RadiusTwoRawTwoJet :=
  ℝ × ((R3 →L[ℝ] ℝ) × (R3 →L[ℝ] (R3 →L[ℝ] ℝ)))

theorem finiteDimensional_radiusTwoRawTwoJet : FiniteDimensional ℝ RadiusTwoRawTwoJet :=
  inferInstance

theorem differentiableAt_radiusTwoSmoothSourceResponse
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    DifferentiableAt ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p :=
  ((radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).2.1.contDiffAt
    (radiusTwoOpens.isOpen.mem_nhds hp)).differentiableAt (by simp)

theorem differentiableAt_fderiv_radiusTwoSmoothSourceResponse
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    DifferentiableAt ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p := by
  have hSmooth := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).2.1
  have hDSmooth : ContDiffOn ℝ ∞
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) (radiusTwoOpens : Set R3) :=
    hSmooth.fderiv_of_isOpen radiusTwoOpens.isOpen (by simp)
  exact (hDSmooth.contDiffAt (radiusTwoOpens.isOpen.mem_nhds hp)).differentiableAt (by simp)

theorem radiusTwoSmoothSourceResponse_fderiv_add
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f h : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f+h)) p =
      fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p +
        fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg h) p := by
  rw [radiusTwoSmoothSourceResponse_add]
  exact fderiv_add (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg f p hp)
    (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg h p hp)

theorem radiusTwoSmoothSourceResponse_fderiv_smul
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (c : ℝ) (f : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (c • f)) p =
      c • fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p := by
  rw [radiusTwoSmoothSourceResponse_smul]
  exact fderiv_const_smul (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg f p hp) c

theorem radiusTwoSmoothSourceResponse_second_fderiv_add
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f h : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f+h))) p =
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p +
        fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg h)) p := by
  have hNear : fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f+h)) =ᶠ[𝓝 p]
      (fun x => fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) x +
        fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg h) x) := by
    filter_upwards [radiusTwoOpens.isOpen.mem_nhds hp] with x hx
    exact radiusTwoSmoothSourceResponse_fderiv_add hreg hcalc g hg f h x hx
  exact hNear.fderiv_eq.trans
    (fderiv_fun_add (differentiableAt_fderiv_radiusTwoSmoothSourceResponse hreg hcalc g hg f p hp)
      (differentiableAt_fderiv_radiusTwoSmoothSourceResponse hreg hcalc g hg h p hp))

theorem radiusTwoSmoothSourceResponse_second_fderiv_smul
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (c : ℝ) (f : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (c • f))) p =
      c • fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p := by
  have hNear : fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (c • f)) =ᶠ[𝓝 p]
      (fun x => c • fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) x) := by
    filter_upwards [radiusTwoOpens.isOpen.mem_nhds hp] with x hx
    exact radiusTwoSmoothSourceResponse_fderiv_smul hreg hcalc g hg c f x hx
  exact hNear.fderiv_eq.trans
    (fderiv_fun_const_smul (differentiableAt_fderiv_radiusTwoSmoothSourceResponse hreg hcalc g hg f p hp) c)

def radiusTwoSmoothSourceJet
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (f : 𝓓(fixedExteriorSourceOpens, ℝ)) : RadiusTwoRawTwoJet :=
  (radiusTwoSmoothSourceResponse hreg hcalc g hg f p,
    (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p,
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p))

def radiusTwoSmoothSourceJetLinear
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3)) :
    𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] RadiusTwoRawTwoJet where
  toFun := radiusTwoSmoothSourceJet hreg hcalc g hg p
  map_add' f h := by
    apply Prod.ext
    · exact congrFun (radiusTwoSmoothSourceResponse_add hreg hcalc g hg f h) p
    · apply Prod.ext
      · exact radiusTwoSmoothSourceResponse_fderiv_add hreg hcalc g hg f h p hp
      · exact radiusTwoSmoothSourceResponse_second_fderiv_add hreg hcalc g hg f h p hp
  map_smul' c f := by
    apply Prod.ext
    · exact congrFun (radiusTwoSmoothSourceResponse_smul hreg hcalc g hg c f) p
    · apply Prod.ext
      · exact radiusTwoSmoothSourceResponse_fderiv_smul hreg hcalc g hg c f p hp
      · exact radiusTwoSmoothSourceResponse_second_fderiv_smul hreg hcalc g hg c f p hp

theorem radiusTwoSmoothSourceJetLinear_apply
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3)) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSmoothSourceJetLinear hreg hcalc g hg p hp f =
      (radiusTwoSmoothSourceResponse hreg hcalc g hg f p,
        (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p,
          fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p)) := rfl

theorem radiusTwoSmoothSourceResponse_second_derivative_symmetric
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) (v w : R3) :
    fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p v w =
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p w v := by
  have hNear : ∀ᶠ x in 𝓝 p, HasFDerivAt (radiusTwoSmoothSourceResponse hreg hcalc g hg f)
      (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) x) x := by
    filter_upwards [radiusTwoOpens.isOpen.mem_nhds hp] with x hx
    exact (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg f x hx).hasFDerivAt
  exact second_derivative_symmetric_of_eventually hNear
    (differentiableAt_fderiv_radiusTwoSmoothSourceResponse hreg hcalc g hg f p hp).hasFDerivAt v w

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.RadiusTwoRawTwoJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.finiteDimensional_radiusTwoRawTwoJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.differentiableAt_radiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.differentiableAt_fderiv_radiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_fderiv_add
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_fderiv_smul
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_second_fderiv_add
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_second_fderiv_smul
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceJetLinear
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceJetLinear_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_second_derivative_symmetric
