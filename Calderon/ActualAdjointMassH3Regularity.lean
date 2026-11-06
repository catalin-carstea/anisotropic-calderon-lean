import Calderon.ActualAdjointMassH3Forcing
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

/-- The given all-order fixed principal regularity upgrades the SAME weak
adjoint solution, already known in H², to H³ when its actual forcing is H¹.
No stronger regularity premise is added. -/
theorem exists_adjointMass_H3_regularity_lift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : MatrixField) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (closedBall (0 : R3) 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
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
    ∃ U : BallSobolev 3,
      TauCeti.Wkp.firstOrder 2 U = (u : BallH1) := by
  let m : BallSobolev 1 :=
    coefficientMultiplier hcalc 1 M2 (nativeLowerOrderL 1 V)
  have hu0 : TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta 0 (TauCeti.Wkp.value 1 (f-m)) u :=
    adjointMass_zeroMass_highForcing hcalc a hcoeff beta hbeta K hK hz
      M1 M2 hM f u V hV hu
  obtain ⟨c,hc,hregular⟩ := hreg 1 a lam Lam hsmooth hell hcoeff
  obtain ⟨U,hU,hnorm⟩ := exists_supportedDrift_principal_regularity_lift
    hcalc 1 a hcoeff c hregular beta hbeta K hK hz (f-m) u V hV hu0
  exact ⟨U,hU⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
