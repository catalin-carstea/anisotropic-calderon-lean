import Calderon.RadiusTwoNormalizedCutoffCoefficients
import Calderon.CoefficientMultiplier
import Calderon.SobolevDivergenceAssembly

/-! EXPANSION-order-forcing.json precedes actual all-order normalized cutoff forcing. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local irreducible] TauCeti.sobolevStage

def radiusTwoNormalizedCutoffOrderForcingL
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (η : SmoothData) :
    BallSobolev (k+1) →L[ℝ] BallSobolev k :=
  (-4 : ℝ) • (∑ i : Fin 3,
    (coefficientMultiplier hcalc k (radiusTwoNormalizedCutoffFluxCoefficient k g hg η i)).comp
      (unitBallCoordinateDerivativeL hcalc k i)) -
    (4 : ℝ) • (coefficientMultiplier hcalc k
      (radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η)).comp
        (TauCeti.Wkp.lowerOrderL k)

lemma radiusTwoNormalizedCutoffOrderForcingL_apply
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (η : SmoothData) (U : BallSobolev (k+1)) :
    radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U =
      (-4 : ℝ) • (∑ i : Fin 3,
        coefficientMultiplier hcalc k (radiusTwoNormalizedCutoffFluxCoefficient k g hg η i)
          (unitBallCoordinateDerivativeL hcalc k i U)) -
        (4 : ℝ) • coefficientMultiplier hcalc k
          (radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η)
            (TauCeti.Wkp.lowerOrder k U) := by
  simp only [radiusTwoNormalizedCutoffOrderForcingL,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  rfl

lemma radiusTwoNormalizedCutoffOrderForcingL_value_ae
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (η : SmoothData) (U : BallSobolev (k+1)) :
    TauCeti.Wkp.value k (radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => (-4 : ℝ) * (∑ i : Fin 3, smoothMetricCutoffFlux g η i ((2 : ℝ) • x) *
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) x) i) -
          4 * (smoothMetricCutoffFluxDivergence g hg η).1 ((2 : ℝ) • x) *
            TauCeti.Wkp.value (k+1) U x := by
  trace "PROOF ENTER actual all-order cutoff forcing value"
  let T (i : Fin 3) : BallSobolev k := coefficientMultiplier hcalc k
    (radiusTwoNormalizedCutoffFluxCoefficient k g hg η i)
      (unitBallCoordinateDerivativeL hcalc k i U)
  let V : BallSobolev k := coefficientMultiplier hcalc k
    (radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η) (TauCeti.Wkp.lowerOrder k U)
  have hi (i : Fin 3) : TauCeti.Wkp.value k (T i)
      =ᵐ[(volume : Measure R3).restrict ballOpens] fun x =>
        smoothMetricCutoffFlux g η i ((2 : ℝ) • x) *
          (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) x) i := by
    have hm := coefficientMultiplier_value_ae hcalc k
      (radiusTwoNormalizedCutoffFluxCoefficient k g hg η i)
        (unitBallCoordinateDerivativeL hcalc k i U)
    have hd := unitBallCoordinateDerivativeL_value_ae hcalc k i U
    filter_upwards [hm,hd,ae_restrict_mem ballOpens.isOpen.measurableSet] with x hm hd hx
    change TauCeti.Wkp.value k (coefficientMultiplier hcalc k
      (radiusTwoNormalizedCutoffFluxCoefficient k g hg η i)
        (unitBallCoordinateDerivativeL hcalc k i U)) x = _
    rw [hm,hd,coefficientValue_radiusTwoNormalizedCutoffFluxCoefficient k g hg η i x hx]
  trace "GRADIENT TERMS MADE actual all-order cutoff forcing value"
  have hV : TauCeti.Wkp.value k V
      =ᵐ[(volume : Measure R3).restrict ballOpens] fun x =>
        (smoothMetricCutoffFluxDivergence g hg η).1 ((2 : ℝ) • x) *
          TauCeti.Wkp.value (k+1) U x := by
    have hm := coefficientMultiplier_value_ae hcalc k
      (radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η) (TauCeti.Wkp.lowerOrder k U)
    filter_upwards [hm,ae_restrict_mem ballOpens.isOpen.measurableSet] with x hm hx
    change TauCeti.Wkp.value k (coefficientMultiplier hcalc k
      (radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η) (TauCeti.Wkp.lowerOrder k U)) x = _
    rw [hm,coefficientValue_radiusTwoNormalizedCutoffDivergenceCoefficient k g hg η x hx]
    exact congrArg (fun r : ℝ =>
      (smoothMetricCutoffFluxDivergence g hg η).1 ((2 : ℝ) • x) * r)
      (congrArg (fun v : BallSobolev 0 => (v : R3 → ℝ) x)
        (TauCeti.Wkp.value_succ k U).symm)
  trace "VALUE TERM MADE actual all-order cutoff forcing value"
  have hs : (∑ i : Fin 3, TauCeti.Wkp.value k (T i))
      =ᵐ[(volume : Measure R3).restrict ballOpens] fun x =>
        ∑ i : Fin 3, smoothMetricCutoffFlux g η i ((2 : ℝ) • x) *
          (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) x) i :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun i _ => hi i)
  rw [radiusTwoNormalizedCutoffOrderForcingL_apply]
  change TauCeti.Wkp.valueL k ((-4 : ℝ) • (∑ i : Fin 3, T i) - (4 : ℝ) • V) =ᵐ[_] _
  rw [map_sub,map_smul,map_smul,map_sum]
  have hLeft := (Lp.coeFn_smul (-4 : ℝ) (∑ i : Fin 3, TauCeti.Wkp.value k (T i))).trans
    (hs.const_smul (-4 : ℝ))
  have hRight := (Lp.coeFn_smul (4 : ℝ) (TauCeti.Wkp.value k V)).trans (hV.const_smul (4 : ℝ))
  have hAll := (Lp.coeFn_sub
    ((-4 : ℝ) • (∑ i : Fin 3, TauCeti.Wkp.value k (T i)))
    ((4 : ℝ) • TauCeti.Wkp.value k V)).trans (hLeft.sub hRight)
  filter_upwards [hAll] with x hx
  dsimp only [TauCeti.Wkp.value] at hx ⊢
  simpa only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,mul_assoc] using hx

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffOrderForcingL
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffOrderForcingL_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffOrderForcingL_value_ae
