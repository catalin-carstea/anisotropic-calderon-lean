import Calderon.RadiusTwoNativeContinuousRepresentativeTransport

/-! Full EXPANSION.json precedes genuine native-to-physical smooth representative transport. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma ae_eq_on_inner_closedBall_of_ae_ball
    (f g : R3 → ℝ) (a b : ℝ) (hab : a < b)
    (hAE : f =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) b)] g) :
    ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → g y = f y := by
  have hGlobal : ∀ᵐ y ∂(volume : Measure R3), y ∈ ball (0 : R3) b → f y = g y :=
    (ae_restrict_iff' isOpen_ball.measurableSet).mp hAE
  have hMu : (volume : Measure R3).restrict ballOpens ≤ (volume : Measure R3) :=
    Measure.restrict_le_self
  filter_upwards [hGlobal.filter_mono (ae_mono hMu)] with y hy hyA
  exact (hy (closedBall_subset_ball hab hyA)).symm

lemma radiusTwo_nativeNormalizedSmoothRepresentative_physical_transport
    (w : RadiusTwoH1Zero) (G : R3 → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hG : Continuous G) (hSmooth : ContDiffOn ℝ ∞ G (ball (0 : R3) b))
    (hAE : (TauCeti.W1p.value (radiusTwoNativeZeroDilation w : BallH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) b)] G) :
    Continuous (fun z : R3 => G ((1/2 : ℝ) • z)) ∧
      ContDiffOn ℝ ∞ (fun z : R3 => G ((1/2 : ℝ) • z)) (ball (0 : R3) (2*a)) ∧
      (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))]
          (fun z : R3 => G ((1/2 : ℝ) • z)) := by
  have hUnit := ae_eq_on_inner_closedBall_of_ae_ball
    (TauCeti.W1p.value (radiusTwoNativeZeroDilation w : BallH1) : R3 → ℝ) G a b hab hAE
  rw [value_radiusTwoNativeZeroDilation] at hUnit
  have hUnitPhysical : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → G y = TauCeti.W1p.value (w : RadiusTwoH1) ((2 : ℝ) • y) := by
    filter_upwards [hUnit,radiusTwoNativeL2Dilation_apply_ae
      (TauCeti.W1p.value (w : RadiusTwoH1))] with y hy hD hyA
    exact (hy hyA).trans hD
  have hPhysical : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      (1/2 : ℝ) • z ∈ closedBall (0 : R3) a →
        G ((1/2 : ℝ) • z) = TauCeti.W1p.value (w : RadiusTwoH1) z := by
    filter_upwards [quasiMeasurePreserving_radiusTwo_comp_half.ae hUnitPhysical] with z hz hzA
    have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by
      rw [smul_smul]
      norm_num
    exact (hz hzA).trans (congrArg (fun x : R3 => TauCeti.W1p.value (w : RadiusTwoH1) x) hCancel)
  have hScale : ContDiff ℝ ∞ (fun z : R3 => (1/2 : ℝ) • z) := contDiff_const_smul (1/2 : ℝ)
  have hNorm (z : R3) : ‖(1/2 : ℝ) • z‖ = (1/2 : ℝ) * ‖z‖ := by
    rw [norm_smul]
    norm_num
  have hMaps : MapsTo (fun z : R3 => (1/2 : ℝ) • z)
      (ball (0 : R3) (2*a)) (ball (0 : R3) b) := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [hNorm]
    have hzNorm : ‖z‖ < 2*a := mem_ball_zero_iff.mp hz
    linarith
  have hSub : ball (0 : R3) (2*a) ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*a ≤ 2) hz
  have hMu : (volume : Measure R3).restrict (ball (0 : R3) (2*a)) ≤
      (volume : Measure R3).restrict radiusTwoOpens := Measure.restrict_mono_set volume hSub
  refine ⟨hG.comp hScale.continuous,hSmooth.comp hScale.contDiffOn hMaps,?_⟩
  filter_upwards [hPhysical.filter_mono (ae_mono hMu),ae_restrict_mem isOpen_ball.measurableSet]
    with z hz hzBall
  have hzA : (1/2 : ℝ) • z ∈ closedBall (0 : R3) a := by
    apply mem_closedBall.mpr
    rw [dist_zero_right,hNorm]
    have hzNorm : ‖z‖ < 2*a := mem_ball_zero_iff.mp hzBall
    linarith
  exact (hz hzA).symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.ae_eq_on_inner_closedBall_of_ae_ball
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_nativeNormalizedSmoothRepresentative_physical_transport
