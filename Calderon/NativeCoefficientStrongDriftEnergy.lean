import Calderon.NativeWeightedDriftFluxGreen

/-! Expanded first in EXPANSION-actual-rotation-guarded-strong-identification-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma value_fullDriftMultiplierSum_eq_supportedDriftL
    (hcalc : FixedSobolevCalculus) (G : Fin 3 → SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0)
    (hG : ∀ j x, coefficientValue 1 (G j) x = beta x j) (U : BallSobolev 2) :
    TauCeti.Wkp.value 0 ((∑ j : Fin 3, (coefficientMultiplier hcalc 0 (G j)).comp
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 j)) U) =
      supportedDriftL hcalc 0 beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U) := by
  let T (j : Fin 3) : BallSobolev 0 := coefficientMultiplier hcalc 0 (G j)
    (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 j U)
  have hj (j : Fin 3) : TauCeti.Wkp.value 0 (T j) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => beta x j * (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) j := by
    have hm := coefficientMultiplier_value_ae hcalc 0 (G j)
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 j U)
    have hd := ordinaryLowerOrderCoordinateDerivative_value_ae hcalc 0 j U
    filter_upwards [hm,hd] with x hm hd
    change TauCeti.Wkp.value 0 (coefficientMultiplier hcalc 0 (G j)
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 j U)) x = _
    rw [hm,hd,hG]
  have hs : TauCeti.Wkp.value 0 ((∑ j : Fin 3, (coefficientMultiplier hcalc 0 (G j)).comp
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 j)) U)
      =ᵐ[((volume : Measure R3).restrict ballOpens)] fun x =>
        ∑ j : Fin 3, beta x j * (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) j := by
    change TauCeti.Wkp.valueL 0 (∑ j : Fin 3, T j) =ᵐ[_] _
    rw [map_sum]
    exact (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun j _ => hj j)
  have hr := supportedDriftL_value_ae hcalc 0 beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U)
  simp only [TauCeti.Wkp.value_zero,TauCeti.Wkp.firstOrder_zero] at hr
  exact Lp.ext (hs.trans hr.symm)

lemma principal_add_fullDriftMultiplierSum_energy
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (G : Fin 3 → SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0)
    (hG : ∀ j x, coefficientValue 1 (G j) x = beta x j)
    (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0 ((ordinaryPrincipalL hcalc 0 F +
        ∑ j : Fin 3, (coefficientMultiplier hcalc 0 (G j)).comp
          (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 j)) U)) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have hp := ordinaryPrincipalL_energy hcalc 0 F U v
  have hs := coefficient_energyFormH1_eq_principal_add_supportedDrift_inner
    hcalc F beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)
  rw [TauCeti.PDE.dirichletForcing_apply] at hp ⊢
  rw [ContinuousLinearMap.add_apply,TauCeti.Wkp.value_add,inner_add_left,hp,
    value_fullDriftMultiplierSum_eq_supportedDriftL hcalc G beta hbeta K hK hz hG U]
  exact hs.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_fullDriftMultiplierSum_eq_supportedDriftL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.principal_add_fullDriftMultiplierSum_energy
