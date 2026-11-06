import Calderon.SmoothMetricCutoffFlux
import Calderon.CoefficientJetSpace
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-! EXPANSION.json precedes the actual normalized full-metric cutoff coefficient jets. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

def radiusTwoNormalizedCutoffCoefficientBump : ContDiffBump (0 : R3) :=
  ⟨2,3,by norm_num,by norm_num⟩

def radiusTwoNormalizedCutoffFluxCoefficient
    (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (η : SmoothData) (i : Fin 3) : SmoothCoefficientJets (k+1) :=
  compactCoefficient (k+1)
    (fun x : R3 => radiusTwoNormalizedCutoffCoefficientBump x *
      smoothMetricCutoffFlux g η i ((2 : ℝ) • x))
    (by
      have hScale : ContDiff ℝ ∞ (fun x : R3 => (2 : ℝ) • x) := contDiff_const_smul 2
      exact radiusTwoNormalizedCutoffCoefficientBump.contDiff.mul
        ((contDiff_smoothMetricCutoffFlux g hg η i).comp hScale))
    radiusTwoNormalizedCutoffCoefficientBump.hasCompactSupport.mul_right

def radiusTwoNormalizedCutoffDivergenceCoefficient
    (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (η : SmoothData) : SmoothCoefficientJets (k+1) :=
  compactCoefficient (k+1)
    (fun x : R3 => radiusTwoNormalizedCutoffCoefficientBump x *
      (smoothMetricCutoffFluxDivergence g hg η).1 ((2 : ℝ) • x))
    (by
      have hScale : ContDiff ℝ ∞ (fun x : R3 => (2 : ℝ) • x) := contDiff_const_smul 2
      exact radiusTwoNormalizedCutoffCoefficientBump.contDiff.mul
        ((smoothMetricCutoffFluxDivergence g hg η).2.comp hScale))
    radiusTwoNormalizedCutoffCoefficientBump.hasCompactSupport.mul_right

lemma radiusTwoNormalizedCutoffCoefficientBump_eq_one
    (x : R3) (hx : x ∈ ballOpens) : radiusTwoNormalizedCutoffCoefficientBump x = 1 := by
  have hxBall : x ∈ ball (0 : R3) 1 := by
    change x ∈ ball (0 : R3) 1 at hx
    exact hx
  apply radiusTwoNormalizedCutoffCoefficientBump.one_of_mem_closedBall
  exact mem_closedBall_zero_iff.mpr
    ((mem_ball_zero_iff.mp hxBall).le.trans (by norm_num [radiusTwoNormalizedCutoffCoefficientBump]))

lemma coefficientValue_radiusTwoNormalizedCutoffFluxCoefficient
    (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (η : SmoothData) (i : Fin 3) (x : R3) (hx : x ∈ ballOpens) :
    coefficientValue (k+1) (radiusTwoNormalizedCutoffFluxCoefficient k g hg η i) x =
      smoothMetricCutoffFlux g η i ((2 : ℝ) • x) := by
  unfold radiusTwoNormalizedCutoffFluxCoefficient
  rw [coefficientValue_compactCoefficient]
  rw [radiusTwoNormalizedCutoffCoefficientBump_eq_one x hx,one_mul]

lemma coefficientValue_radiusTwoNormalizedCutoffDivergenceCoefficient
    (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (η : SmoothData) (x : R3) (hx : x ∈ ballOpens) :
    coefficientValue (k+1) (radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η) x =
      (smoothMetricCutoffFluxDivergence g hg η).1 ((2 : ℝ) • x) := by
  unfold radiusTwoNormalizedCutoffDivergenceCoefficient
  rw [coefficientValue_compactCoefficient]
  rw [radiusTwoNormalizedCutoffCoefficientBump_eq_one x hx,one_mul]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffCoefficientBump
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffFluxCoefficient
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffDivergenceCoefficient
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffCoefficientBump_eq_one
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coefficientValue_radiusTwoNormalizedCutoffFluxCoefficient
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coefficientValue_radiusTwoNormalizedCutoffDivergenceCoefficient
