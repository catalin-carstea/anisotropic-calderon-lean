import Calderon.RadiusTwoFiniteRowCutoffSmoothness
import Calderon.NativeCoordinateWordClassicalGraph
import Calderon.RadiusTwoNativeL2Dilation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets

theorem radiusTwo_finiteRow_cutoff_native_word_value_ae
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3))
    (η : 𝓓(radiusTwoOpens, ℝ))
    (hPole : ∀ i : Fin m, (p i : R3) ∉ tsupport (η : R3 → ℝ))
    (u : RadiusTwoH1Zero)
    (hu : (TauCeti.W1p.value (u : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => η z * ∑ i : Fin m, a i * G (p i) z))
    (s : ℕ) (w : List (Fin 3)) (U : BallSobolev (s + w.length))
    (hU : TauCeti.Wkp.value (s + w.length) U =
      radiusTwoNativeL2Dilation (TauCeti.W1p.value (u : RadiusTwoH1))) :
    (TauCeti.Wkp.value s (unitBallCoordinateWordL hcalc w.length s w.get U) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      coordinateFieldWordPartial w (fun x => η ((2 : ℝ) • x) *
        ∑ i : Fin m, a i * G (p i) ((2 : ℝ) • x)) := by
  have hSmooth := (contDiffOn_radiusTwo_finiteRow_cutoff hreg hcalc g hg K G hData
    m a p η hPole).2
  have hDilation := radiusTwoNativeL2Dilation_apply_ae (TauCeti.W1p.value (u : RadiusTwoH1))
  have hPullback := quasiMeasurePreserving_radiusTwo_comp_two.ae_eq_comp hu
  have hValue : (TauCeti.Wkp.value (s + w.length) U : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => η ((2 : ℝ) • x) * ∑ i : Fin m, a i * G (p i) ((2 : ℝ) • x)) := by
    filter_upwards [hDilation, hPullback] with x hx hy
    have hPoint := congrArg (fun v : BallSobolev 0 => v x) hU
    exact hPoint.trans (hx.trans hy)
  exact unitBallCoordinateWordL_list_value_ae_of_contDiffOn hcalc s w U _ hSmooth hValue

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_finiteRow_cutoff_native_word_value_ae
