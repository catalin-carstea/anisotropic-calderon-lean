import Calderon.ActualReferenceAdjointH3MassCoherence
import Calderon.NativeScalarMassPrincipalRegularity
import Calderon.SupportedDriftPrincipalRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

private lemma value_sub_one (X Y : BallSobolev 1) :
    TauCeti.Wkp.value 1 (X-Y) = TauCeti.Wkp.value 1 X - TauCeti.Wkp.value 1 Y := by
  change (TauCeti.Wkp.valueL 1) (X-Y) =
    (TauCeti.Wkp.valueL 1) X - (TauCeti.Wkp.valueL 1) Y
  exact map_sub _ X Y

/-- The given all-order fixed principal regularity upgrades the SAME weak
adjoint solution, already known in H², to H³ when its actual forcing is H¹.
No stronger regularity premise is added. -/
theorem adjointMass_zeroMass_highForcing
    (hcalc : FixedSobolevCalculus)
    (a : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (M1 : SmoothCoefficientJets 1) (M2 : SmoothCoefficientJets 2)
    (hM : coefficientValue 2 M2 = coefficientValue 1 M1)
    (f : BallSobolev 1) (u : BallH1Zero) (V : BallSobolev 2)
    (hV : TauCeti.Wkp.firstOrder 1 V = (u : BallH1))
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (coefficientValue 1 M1) (TauCeti.Wkp.value 1 f) u) :
    TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta 0
      (TauCeti.Wkp.value 1
        (f - coefficientMultiplier hcalc 1 M2 (nativeLowerOrderL 1 V))) u := by
  let m : BallSobolev 1 :=
    coefficientMultiplier hcalc 1 M2 (nativeLowerOrderL 1 V)
  have hMass : TauCeti.Wkp.value 1 m = nativeCoefficientMassL hcalc M1 (u : BallH1) := by
    have h := value_adjointMass_one_eq_zero_of_same_coefficient hcalc M2 M1 hM V
    rw [nativeH2FirstOrderL_apply, hV] at h
    simpa only [TauCeti.Wkp.value_zero] using h
  have hu0 := supportedDrift_zeroMass_weakSolution_of_mass_weakSolution
    hcalc a hcoeff beta hbeta K hK hz M1 (TauCeti.Wkp.value 1 f) u hu
  have hu0' : TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta 0 (TauCeti.Wkp.value 1 (f-m)) u := by
    have hforce : TauCeti.Wkp.value 1 (f-m) =
        TauCeti.Wkp.value 1 f - nativeCoefficientMassL hcalc M1 (u : BallH1) := by
      rw [value_sub_one,hMass]
    exact hforce.symm ▸ hu0
  exact hu0'

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
