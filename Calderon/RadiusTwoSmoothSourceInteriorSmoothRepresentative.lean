import Calderon.RadiusTwoNativeSmoothRepresentativeTransport
import Calderon.RadiusTwoNormalizedSmoothSourceCoherence

/-! Full EXPANSION.json precedes the actual physical smooth-source representative caller. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

lemma exists_radiusTwoSmoothSource_contDiffOn_innerBall
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) (2*a)) ∧
      (TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] G := by
  let b : ℝ := (a+1)/2
  have hb : 0 < b := by dsimp only [b]; linarith
  have hab : a < b := by dsimp only [b]; linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  obtain ⟨G,hG,hSmooth,hAE⟩ :=
    exists_radiusTwoNormalizedSmoothSource_contDiffOn_innerBall hreg hcalc g hg F b hb hb1
  have hTransport := radiusTwo_nativeNormalizedSmoothRepresentative_physical_transport
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) G a b ha hab hb1 hG hSmooth hAE
  exact ⟨(fun z : R3 => G ((1/2 : ℝ) • z)),hTransport.1,hTransport.2.1,hTransport.2.2⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_contDiffOn_innerBall
