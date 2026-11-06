import Calderon.NativeCoefficientFluxTrace
import Calderon.CoordinateWeakIntegration

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def coefficientFirstJets (F : SmoothCoefficientJets 2) : SmoothCoefficientJets 1 :=
  compactCoefficient 1 (coefficientValue 2 F) (contDiff_coefficientValue 2 F)
    (hasCompactSupport_coefficientValue 2 F)

theorem coefficientValue_coefficientFirstJets (F : SmoothCoefficientJets 2) :
    coefficientValue 1 (coefficientFirstJets F) = coefficientValue 2 F :=
  coefficientValue_compactCoefficient 1 (coefficientValue 2 F)
    (contDiff_coefficientValue 2 F) (hasCompactSupport_coefficientValue 2 F)

def nativeCoefficientH1ProductL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientJets 2) : BallH1 →L[ℝ] BallH1 :=
  (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) 0).comp (coefficientMultiplier hcalc 1 F)

theorem nativeCoefficientH1ProductL_eq_contDiffSMulL
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coefficientSmoothData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coefficientSmoothData F).1 x‖ ≤ M)
    (u : BallH1) :
    nativeCoefficientH1ProductL hcalc F u =
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (coefficientSmoothData F).1 (coefficientSmoothData F).2 hM hm hg u := by
  change TauCeti.Wkp.firstOrder 0 (coefficientMultiplier hcalc 1 F u) = _
  have he := firstOrder_coefficientMultiplier_eq_contDiffSMulL hcalc F u hM hm hg
  have hu : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0 (u : BallSobolev 1) = u := rfl
  exact he.trans (congrArg
    (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (coefficientSmoothData F).1 (coefficientSmoothData F).2 hM hm hg) hu)

theorem nativeCoefficientH1ProductL_value_ae
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2) (u : BallH1) :
    TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc F u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue 2 F x * TauCeti.W1p.value u x := by
  change TauCeti.W1p.value (TauCeti.Wkp.firstOrder 0 (coefficientMultiplier hcalc 1 F u)) =ᵐ[_] _
  rw [TauCeti.Wkp.value_firstOrder]
  exact coefficientMultiplier_value_ae hcalc 1 F u

theorem nativeCoefficientH1ProductL_coordinateGradient_ae
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2) (u : BallH1) (i : Fin 3) :
    unitBallCoordinateGradientL i (nativeCoefficientH1ProductL hcalc F u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue 2 F x * (TauCeti.W1p.gradient u x) i +
        TauCeti.W1p.value u x * (gradient (coefficientValue 2 F) x) i := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  have hp := nativeCoefficientH1ProductL_eq_contDiffSMulL hcalc F hM hm hg u
  have hgrad := TauCeti.W1p.gradient_contDiffSMul_ae
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
    (coefficientSmoothData F).2 hM hm hg u
  rw [TauCeti.W1p.contDiffSMulL_apply] at hp
  filter_upwards [unitBallCoordinateGradientL_ae i (nativeCoefficientH1ProductL hcalc F u),
    hgrad] with x hcoord hprod
  rw [hcoord,hp,hprod]
  simp only [coefficientSmoothData, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
