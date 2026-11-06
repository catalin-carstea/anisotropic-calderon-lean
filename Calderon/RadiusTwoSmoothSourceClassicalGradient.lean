import Calderon.RadiusTwoSmoothSourceInteriorSmoothRepresentative
import Calderon.NativeSmoothValueClassicalGradient

/-! Full EXPANSION.json precedes this actual-source classical-gradient caller. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

lemma exists_radiusTwoSmoothSource_valueGradient_innerBall
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (H : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) (2*a)) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] G) ∧
      ((TauCeti.W1p.gradient (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] gradient G) := by
  obtain ⟨G,hG,hSmooth,hValue⟩ :=
    exists_radiusTwoSmoothSource_contDiffOn_innerBall hreg hcalc g hg H a ha ha1
  let Omega : Opens R3 := ⟨ball (0 : R3) (2*a),isOpen_ball⟩
  have hSub : Omega ≤ radiusTwoOpens := by
    change ball (0 : R3) (2*a) ⊆ ball (0 : R3) 2
    exact ball_subset_ball (by linarith)
  have hGradient := native_gradient_ae_eq_gradient_of_contDiffOn_value
    Omega radiusTwoOpens hSub
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1)
    G hSmooth hValue
  exact ⟨G,hG,hSmooth,hValue,hGradient⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_valueGradient_innerBall
