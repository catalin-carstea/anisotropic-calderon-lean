import Calderon.RadiusTwoNormalizedCutoffOrderForcing
import Calderon.RadiusTwoNativeDilationJets
import Calderon.RadiusTwoFixedRowCutoffForcing

/-! EXPANSION-order-forcing-dilation.json precedes exact physical/native forcing correspondence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoNormalizedCutoffForcing_scalar_identity
    (J v : Fin 3 → ℝ) (d u : ℝ) :
    (-4 : ℝ) * (∑ i : Fin 3, J i * (2 * v i)) - 4 * d * u =
      4 * ((-2 : ℝ) * (∑ i : Fin 3, J i * v i) - d * u) := by
  have hSum : (∑ i : Fin 3, J i * (2 * v i)) =
      2 * (∑ i : Fin 3, J i * v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hSum]
  ring

lemma radiusTwoNormalizedCutoffOrderForcing_value_eq_dilation
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (η : SmoothData)
    (w : RadiusTwoH1Zero) (U : BallSobolev (k+1))
    (hU : TauCeti.Wkp.firstOrder k U = (radiusTwoNativeZeroDilation w : BallH1)) :
    TauCeti.Wkp.value k (radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U) =
      (4 : ℝ) • radiusTwoNativeL2Dilation
        (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1)) := by
  trace "PROOF ENTER actual cutoff high-order forcing dilation"
  have hV : TauCeti.Wkp.value (k+1) U =
      radiusTwoNativeL2Dilation (TauCeti.W1p.value (w : RadiusTwoH1)) :=
    (TauCeti.Wkp.value_firstOrder k U).symm.trans
      ((congrArg (fun v : BallH1 => TauCeti.W1p.value v) hU).trans
        (value_radiusTwoNativeZeroDilation w))
  have hG : TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) =
      (2 : ℝ) • radiusTwoNativeL2Dilation (TauCeti.W1p.gradient (w : RadiusTwoH1)) :=
    (congrArg (fun v : BallH1 => TauCeti.W1p.gradient v) hU).trans
      (gradient_radiusTwoNativeZeroDilation w)
  trace "ACTUAL VALUE GRADIENT DILATION MADE high-order forcing"
  apply Lp.ext
  have hFComp := quasiMeasurePreserving_radiusTwo_comp_two.ae_eq_comp
    (radiusTwoFixedRowCutoffForcingLp_apply_ae g hg η (w : RadiusTwoH1))
  filter_upwards [radiusTwoNormalizedCutoffOrderForcingL_value_ae hcalc k g hg η U,
    radiusTwoNativeL2Dilation_apply_ae
      (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1)),
    hFComp,
    Lp.coeFn_smul (4 : ℝ) (radiusTwoNativeL2Dilation
      (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))),
    Lp.coeFn_smul (2 : ℝ) (radiusTwoNativeL2Dilation (TauCeti.W1p.gradient (w : RadiusTwoH1))),
    radiusTwoNativeL2Dilation_apply_ae (TauCeti.W1p.gradient (w : RadiusTwoH1)),
    radiusTwoNativeL2Dilation_apply_ae (TauCeti.W1p.value (w : RadiusTwoH1))]
      with x hFormula hFDil hFVal hFour hTwo hGradDil hValDil
  change radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1) ((2 : ℝ) • x) =
    radiusTwoFixedRowCutoffForcing g hg η (w : RadiusTwoH1) ((2 : ℝ) • x) at hFVal
  have hGradPoint : TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) x =
      (2 : ℝ) • TauCeti.W1p.gradient (w : RadiusTwoH1) ((2 : ℝ) • x) := by
    rw [hG]
    exact hTwo.trans (congrArg (fun v : R3 => (2 : ℝ) • v) hGradDil)
  have hValuePoint : TauCeti.Wkp.value (k+1) U x =
      TauCeti.W1p.value (w : RadiusTwoH1) ((2 : ℝ) • x) := by
    rw [hV]
    exact hValDil
  rw [hFormula,hFour]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hFDil,hFVal]
  rw [hGradPoint,hValuePoint]
  unfold radiusTwoFixedRowCutoffForcing
  simp only [PiLp.smul_apply,smul_eq_mul,MetricVolume.coordinateVector,
    EuclideanSpace.inner_single_right,one_mul,conj_trivial]
  exact radiusTwoNormalizedCutoffForcing_scalar_identity
    (fun i => smoothMetricCutoffFlux g η i ((2 : ℝ) • x))
    (fun i => (TauCeti.W1p.gradient (w : RadiusTwoH1) ((2 : ℝ) • x)) i)
    ((smoothMetricCutoffFluxDivergence g hg η).1 ((2 : ℝ) • x))
    (TauCeti.W1p.value (w : RadiusTwoH1) ((2 : ℝ) • x))

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffForcing_scalar_identity
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffOrderForcing_value_eq_dilation
