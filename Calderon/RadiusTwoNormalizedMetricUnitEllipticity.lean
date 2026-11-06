import Calderon.RadiusTwoNativeSourceFoundation

/-! Full EXPANSION.json precedes focused actual normalized principal ellipticity. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError

theorem exists_unitEllipticity_radiusTwoNormalizedMetric
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (principalCoefficient (enlargedBallNormalizedMetric g 2)) lam Lam := by
  trace "PROOFENTER focused actual normalized metric ellipticity"
  have hGeneric : ∀ (m : MatrixField), IsAdmissibleMetric m →
      ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
        (principalCoefficient m) lam Lam := by
    intro m hm
    exact exists_uniformlyEllipticOn_principalCoefficient m hm
  trace "GENERIC ELLIPTICITY CACHED focused normalized metric"
  obtain ⟨lam,Lam,hClosed⟩ := hGeneric (enlargedBallNormalizedMetric g 2)
    (isAdmissibleMetric_radiusTwoNormalized g hg)
  trace "NORMALIZED ELLIPTICITY SPECIALIZED focused normalized metric"
  exact ⟨lam,Lam,hClosed.mono_set ball_subset_closedBall⟩

end OAI.AnisotropicCalderon.ExteriorSource
