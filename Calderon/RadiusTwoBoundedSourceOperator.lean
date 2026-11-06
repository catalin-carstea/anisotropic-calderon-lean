import Calderon.RadiusTwoSourceAdditivity
import Calderon.RadiusTwoSourceHomogeneity
import Calderon.RadiusTwoSourceBound

/-! EXPANSION.json precedes this bounded realization of the already constructed
actual radius-two source solver. The source is a Lebesgue density. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

def radiusTwoForcingL : RadiusTwoL2 →L[ℝ] StrongDual ℝ RadiusTwoH1Zero :=
  ContinuousLinearMap.bilinearComp (innerSL ℝ)
    (ContinuousLinearMap.id ℝ RadiusTwoL2)
    (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := radiusTwoOpens) (p := 2))

theorem radiusTwoForcingL_apply (f : RadiusTwoL2) :
    radiusTwoForcingL f = TauCeti.PDE.dirichletForcing f := by
  ext v
  simp only [radiusTwoForcingL,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,TauCeti.W1p0.valueL_apply,
    TauCeti.PDE.dirichletForcing_apply]

def radiusTwoSourceSolutionL (g : MatrixField) (hg : IsAdmissibleMetric g) :
    RadiusTwoL2 →L[ℝ] RadiusTwoH1Zero :=
  let L : RadiusTwoL2 →ₗ[ℝ] RadiusTwoH1Zero :=
    { toFun := radiusTwoSourceSolution g hg
      map_add' := radiusTwoSourceSolution_add g hg
      map_smul' := fun c f => by
        simpa only [RingHom.id_apply] using radiusTwoSourceSolution_smul g hg c f }
  L.mkContinuous (Classical.choose (exists_bound_radiusTwoSourceSolution g hg))
    (Classical.choose_spec (exists_bound_radiusTwoSourceSolution g hg)).2

theorem radiusTwoSourceSolutionL_apply (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : RadiusTwoL2) :
    radiusTwoSourceSolutionL g hg f = radiusTwoSourceSolution g hg f := by
  rfl

theorem norm_radiusTwoSourceSolution_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : RadiusTwoL2) :
    ‖radiusTwoSourceSolution g hg f‖ ≤ ‖radiusTwoSourceSolutionL g hg‖ * ‖f‖ := by
  rw [← radiusTwoSourceSolutionL_apply]
  exact (radiusTwoSourceSolutionL g hg).le_opNorm f

end OAI.AnisotropicCalderon.ExteriorSource
