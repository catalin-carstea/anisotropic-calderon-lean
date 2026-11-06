import Calderon.ClosedCoefficientMultiplier
import Calderon.CommonSupportMatrixInverse
import Calderon.CoordinateDriftFluxEnergy
import Calderon.FiniteForcingEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

/-! All tests are actual BallH1; c=0 is literal selected mass-zero energy. -/

def nativeSmoothDriftField (G : Fin 3 → SmoothCoefficientJets 1) : R3 → R3 :=
  fun x => WithLp.toLp 2 (fun i => coefficientValue 1 (G i) x)

lemma nativeSmoothDriftField_coordinate (G : Fin 3 → SmoothCoefficientJets 1) (x : R3) (i : Fin 3) :
    nativeSmoothDriftField G x i = coefficientValue 1 (G i) x := rfl

def nativeSmoothCoefficientFullEnergyL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (G : Fin 3 → SmoothCoefficientJets 1) :
    BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  let E0 := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)
  let D : Fin 3 → BallH1 →L[ℝ] E0 := unitBallCoordinateGradientL
  let V : BallH1 →L[ℝ] E0 := TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
  (∑ i : Fin 3, ∑ j : Fin 3,
    (forcingFromValueL (D i)).comp ((coefficientMultiplier hcalc 0 (F i j)).comp (D j))) +
    ∑ i : Fin 3, (forcingFromValueL V).comp ((coefficientMultiplier hcalc 0 (G i)).comp (D i))

lemma nativeSmoothCoefficientFullEnergyL_apply_sum (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (G : Fin 3 → SmoothCoefficientJets 1) (u v : BallH1) :
    nativeSmoothCoefficientFullEnergyL hcalc F G u v =
      (∑ i : Fin 3, ∑ j : Fin 3, ⟪coefficientMultiplier hcalc 0 (F i j) (unitBallCoordinateGradientL j u),
        unitBallCoordinateGradientL i v⟫_ℝ) +
      ∑ i : Fin 3, ⟪coefficientMultiplier hcalc 0 (G i) (unitBallCoordinateGradientL i u),TauCeti.W1p.value v⟫_ℝ := by
  simp only [nativeSmoothCoefficientFullEnergyL,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,forcingFromValueL_apply_apply]
  rfl

lemma nativeSmoothPrincipalFlux_ae (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (u : BallH1) (i j : Fin 3) :
    coefficientMultiplier hcalc 0 (F i j) (unitBallCoordinateGradientL j u) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientMatrixField 1 F x i j * (TauCeti.W1p.gradient u x) j := by
  filter_upwards [coefficientMultiplier_value_ae hcalc 0 (F i j) (unitBallCoordinateGradientL j u),
    unitBallCoordinateGradientL_ae j u] with x hx hg
  simp only [TauCeti.Wkp.value_zero] at hx
  change coefficientMultiplier hcalc 0 (F i j) (unitBallCoordinateGradientL j u) x =
    coefficientValue 1 (F i j) x * (TauCeti.W1p.gradient u x) j
  exact hx.trans (congrArg (fun t : ℝ => coefficientValue 1 (F i j) x*t) hg)

lemma nativeSmoothDriftFlux_ae (hcalc : FixedSobolevCalculus)
    (G : Fin 3 → SmoothCoefficientJets 1) (u : BallH1) (i : Fin 3) :
    coefficientMultiplier hcalc 0 (G i) (unitBallCoordinateGradientL i u) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => nativeSmoothDriftField G x i * (TauCeti.W1p.gradient u x) i := by
  filter_upwards [coefficientMultiplier_value_ae hcalc 0 (G i) (unitBallCoordinateGradientL i u),
    unitBallCoordinateGradientL_ae i u] with x hx hg
  simp only [TauCeti.Wkp.value_zero] at hx
  change coefficientMultiplier hcalc 0 (G i) (unitBallCoordinateGradientL i u) x =
    coefficientValue 1 (G i) x * (TauCeti.W1p.gradient u x) i
  exact hx.trans (congrArg (fun t : ℝ => coefficientValue 1 (G i) x*t) hg)

lemma nativeSmoothCoefficientFullEnergyL_apply (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (G : Fin 3 → SmoothCoefficientJets 1) (u v : BallH1) :
    nativeSmoothCoefficientFullEnergyL hcalc F G u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField 1 F) (nativeSmoothDriftField G) 0 u v := by
  exact (nativeSmoothCoefficientFullEnergyL_apply_sum hcalc F G u v).trans
    (energyFormH1_eq_sum_coordinateFlux_inner_add_drift (coefficientMatrixField 1 F) (nativeSmoothDriftField G) u v
      (fun i j => coefficientMultiplier hcalc 0 (F i j) (unitBallCoordinateGradientL j u))
      (fun i => coefficientMultiplier hcalc 0 (G i) (unitBallCoordinateGradientL i u))
      (nativeSmoothPrincipalFlux_ae hcalc F u) (nativeSmoothDriftFlux_ae hcalc G u)).symm

lemma nativeSmoothCoefficientFullEnergyL_eq_energyFormH1L (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (G : Fin 3 → SmoothCoefficientJets 1)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 1 F x)
      (nativeSmoothDriftField G x) 0) ⊤ ((volume : Measure R3).restrict ballOpens)) :
    nativeSmoothCoefficientFullEnergyL hcalc F G =
      TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := coefficientMatrixField 1 F) (b := nativeSmoothDriftField G) (c := 0) hcoeff := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (nativeSmoothCoefficientFullEnergyL_apply hcalc F G u v).trans
    (TauCeti.PDE.energyFormH1L_apply hcoeff u v).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothDriftField
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothDriftField_coordinate
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullEnergyL_apply_sum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothPrincipalFlux_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothDriftFlux_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullEnergyL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullEnergyL_eq_energyFormH1L
