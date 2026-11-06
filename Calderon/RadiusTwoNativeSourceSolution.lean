import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes the actual radius-two zero-Dirichlet Lax–Milgram construction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def smoothRadiusTwoForcing (F : SmoothData) : RadiusTwoL2 :=
  (memLp_two_radiusTwo_of_continuous F.1 F.2.continuous).toLp F.1

theorem smoothRadiusTwoForcing_ae (F : SmoothData) :
    smoothRadiusTwoForcing F =ᵐ[((volume : Measure R3).restrict radiusTwoOpens)] F.1 :=
  MemLp.coeFn_toLp (memLp_two_radiusTwo_of_continuous F.1 F.2.continuous)

def radiusTwoSourceSolution (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : RadiusTwoL2) : RadiusTwoH1Zero :=
  TauCeti.PDE.weakSolutionDirichlet (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (isCoercive_radiusTwoMetricEnergy g hg) f

theorem radiusTwoSourceSolution_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2) (v : RadiusTwoH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (radiusTwoSourceSolution g hg f : RadiusTwoH1) (v : RadiusTwoH1) =
      TauCeti.PDE.dirichletForcing f v :=
  TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet
    (memLp_radiusTwoMetricEnergyIntegrand g hg) (isCoercive_radiusTwoMetricEnergy g hg) f v

theorem eq_radiusTwoSourceSolution
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2) (w : RadiusTwoH1Zero)
    (hw : ∀ v : RadiusTwoH1Zero,
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (w : RadiusTwoH1) (v : RadiusTwoH1) = TauCeti.PDE.dirichletForcing f v) :
    w = radiusTwoSourceSolution g hg f :=
  TauCeti.PDE.eq_weakSolutionDirichlet (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (isCoercive_radiusTwoMetricEnergy g hg) hw

theorem radiusTwoSourceSolution_smooth_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData) (v : RadiusTwoH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) (v : RadiusTwoH1) =
      ∫ x in radiusTwoOpens, F.1 x * TauCeti.W1p.value (v : RadiusTwoH1) x ∂(volume : Measure R3) := by
  rw [radiusTwoSourceSolution_equation,TauCeti.PDE.dirichletForcing_apply_eq_setIntegral]
  apply integral_congr_ae
  filter_upwards [smoothRadiusTwoForcing_ae F] with x hx
  rw [hx]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.smoothRadiusTwoForcing
#print axioms OAI.AnisotropicCalderon.ExteriorSource.smoothRadiusTwoForcing_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_equation
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eq_radiusTwoSourceSolution
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_smooth_equation
