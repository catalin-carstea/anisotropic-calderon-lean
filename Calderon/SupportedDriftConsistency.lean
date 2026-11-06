import Calderon.SupportedDriftOperator
import Calderon.StrongOperatorEnergy
import Calderon.UniformSmallDriftCoercivity
import Calderon.CoefficientMatrixRegularity
import Calderon.DirichletForcingInjectivity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge


/-- The coordinate of a fixed smooth supported drift, as an actual jet coefficient. -/
def supportedDriftCoefficient (k : ℕ) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ z, z ∉ K → beta z = 0)
    (i : Fin 3) : SmoothCoefficientJets (k + 1) :=
  commonSupportCoefficientFamily (k + 1)
    (fun p : ℝ × R3 => beta p.2 i)
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hbeta).comp contDiff_snd)
    K hK (fun _ z h => by simp [hz z h]) 0

theorem supportedDriftCoefficient_value (k : ℕ) (beta : R3 → R3)
    (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (i : Fin 3) (z : R3) :
    coefficientValue (k + 1) (supportedDriftCoefficient k beta hbeta K hK hz i) z =
      beta z i :=
  coefficientValue_commonSupportCoefficientFamily (k + 1) _ _ K hK _ 0 z

/-- This loses one order, rather than restricting an H^{s+2} drift to H^s. -/
def supportedDriftL (hcalc : FixedSobolevCalculus) (k : ℕ) (beta : R3 → R3)
    (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) : BallSobolev (k + 1) →L[ℝ] BallSobolev k :=
  ∑ i : Fin 3, (coefficientMultiplier hcalc k
    (supportedDriftCoefficient k beta hbeta K hK hz i)).comp
      (unitBallCoordinateDerivativeL hcalc k i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem supportedDriftL_value_ae (hcalc : FixedSobolevCalculus) (k : ℕ)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (U : BallSobolev (k + 1)) :
    TauCeti.Wkp.value k (supportedDriftL hcalc k beta hbeta K hK hz U)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => ∑ i : Fin 3, beta z i *
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) z) i := by
  let T (i : Fin 3) : BallSobolev k := coefficientMultiplier hcalc k
    (supportedDriftCoefficient k beta hbeta K hK hz i)
      (unitBallCoordinateDerivativeL hcalc k i U)
  have hi (i : Fin 3) : TauCeti.Wkp.value k (T i)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => beta z i * (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) z) i := by
    have hmul := coefficientMultiplier_value_ae hcalc k
      (supportedDriftCoefficient k beta hbeta K hK hz i)
      (unitBallCoordinateDerivativeL hcalc k i U)
    have hder := unitBallCoordinateDerivativeL_value_ae hcalc k i U
    apply (hmul.trans (EventuallyEq.mul (EventuallyEq.refl _ _) hder)).trans
    apply Eventually.of_forall
    intro z
    exact congrArg (fun t : ℝ => t *
      (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) z) i)
      (supportedDriftCoefficient_value k beta hbeta K hK hz i z)
  change (TauCeti.Wkp.valueL k) (∑ i : Fin 3, T i) =ᵐ[_] _
  rw [map_sum]
  exact (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun i _ => hi i))

theorem sum_coordinate_mul_eq_inner (b xi : R3) :
    (∑ i : Fin 3, b i * xi i) = inner ℝ b xi := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem supportedDriftL_value_inner_ae (hcalc : FixedSobolevCalculus) (k : ℕ)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (U : BallSobolev (k + 1)) :
    TauCeti.Wkp.value k (supportedDriftL hcalc k beta hbeta K hK hz U)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => inner ℝ (beta z) (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder k U) z) :=
  (supportedDriftL_value_ae hcalc k beta hbeta K hK hz U).trans
    (Eventually.of_forall fun z => sum_coordinate_mul_eq_inner _ _)

/-- A literal equality in native L², including the order-zero boundary case. -/
theorem supportedDriftL_value_eq_firstOrder (hcalc : FixedSobolevCalculus) (k : ℕ)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (U : BallSobolev (k + 1)) :
    TauCeti.Wkp.value k (supportedDriftL hcalc k beta hbeta K hK hz U) =
      supportedDriftL hcalc 0 beta hbeta K hK hz (TauCeti.Wkp.firstOrder k U) := by
  apply Lp.ext
  have h0 := supportedDriftL_value_inner_ae hcalc 0 beta hbeta K hK hz
    (TauCeti.Wkp.firstOrder k U)
  simpa only [TauCeti.Wkp.value_zero, TauCeti.Wkp.firstOrder_zero] using
    (supportedDriftL_value_inner_ae hcalc k beta hbeta K hK hz U).trans h0.symm

/-- Different chosen multiplier and derivative maps are forced to agree at adjacent orders. -/
theorem supportedDriftL_lowerOrder (hcalc : FixedSobolevCalculus) (k : ℕ)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (U : BallSobolev (k + 2)) :
    supportedDriftL hcalc k beta hbeta K hK hz (TauCeti.Wkp.lowerOrder (k + 1) U) =
      TauCeti.Wkp.lowerOrder k (supportedDriftL hcalc (k + 1) beta hbeta K hK hz U) := by
  apply TauCeti.Wkp.ext k
  rw [← TauCeti.Wkp.value_succ]
  rw [supportedDriftL_value_eq_firstOrder, supportedDriftL_value_eq_firstOrder,
    ← TauCeti.Wkp.firstOrder_succ]

/-- The actual strong-domain drift is the preceding-order projection of this one-order map. -/
def supportedStrongDriftL (hcalc : FixedSobolevCalculus) (s : ℕ) (beta : R3 → R3)
    (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  (supportedDriftL hcalc s beta hbeta K hK hz).comp
    ((TauCeti.Wkp.lowerOrderL (s + 1)).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem supportedStrongDriftL_value_eq (hcalc : FixedSobolevCalculus) (s : ℕ)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (U : StrongDirichletSpace s) :
    TauCeti.Wkp.value s (supportedStrongDriftL hcalc s beta hbeta K hK hz U) =
      supportedDriftL hcalc 0 beta hbeta K hK hz
        (strongDirichletProjectionL s U : BallH1) := by
  have hnative := supportedDriftL_value_eq_firstOrder hcalc s beta hbeta K hK hz
    (TauCeti.Wkp.lowerOrder (s + 1) (U : BallSobolev (s + 2)))
  have hprojection :
      TauCeti.Wkp.firstOrder s (TauCeti.Wkp.lowerOrder (s + 1)
        (U : BallSobolev (s + 2))) = (strongDirichletProjectionL s U : BallH1) :=
    (TauCeti.Wkp.firstOrder_succ s (U : BallSobolev (s + 2))).symm.trans
      (strongDirichletProjectionL_apply s U).symm
  have h := hnative.trans (congrArg
    (fun w : BallH1 => supportedDriftL hcalc 0 beta hbeta K hK hz w) hprojection)
  have hsub : (strongDirichletSubmodule s).toSubmodule.subtypeL U =
      (U : BallSobolev (s + 2)) :=
    Submodule.subtypeL_apply (strongDirichletSubmodule s).toSubmodule U
  have hlower : (TauCeti.Wkp.lowerOrderL (s + 1))
      ((strongDirichletSubmodule s).toSubmodule.subtypeL U) =
        TauCeti.Wkp.lowerOrder (s + 1) (U : BallSobolev (s + 2)) :=
    (congrArg (fun V : BallSobolev (s + 2) =>
      (TauCeti.Wkp.lowerOrderL (s + 1)) V) hsub).trans
        (TauCeti.Wkp.lowerOrderL_apply (s + 1) (U : BallSobolev (s + 2)))
  have hstrong : supportedStrongDriftL hcalc s beta hbeta K hK hz U =
      supportedDriftL hcalc s beta hbeta K hK hz
        ((TauCeti.Wkp.lowerOrderL (s + 1))
          ((strongDirichletSubmodule s).toSubmodule.subtypeL U)) := rfl
  exact (congrArg (fun V : BallSobolev s => TauCeti.Wkp.value s V) hstrong).trans
    ((congrArg (fun V : BallSobolev (s + 1) => TauCeti.Wkp.value s
      (supportedDriftL hcalc s beta hbeta K hK hz V)) hlower).trans h)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integral splitting needs only the actual principal density and the constructed L² drift. -/
theorem energyFormH1_eq_principal_add_driftForcing (hcalc : FixedSobolevCalculus)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 a beta 0 u (v : BallH1) =
      TauCeti.PDE.energyFormH1 a 0 0 u (v : BallH1) +
        TauCeti.PDE.dirichletForcing
          (supportedDriftL hcalc 0 beta hbeta K hK hz u) v := by
  let muBall : Measure R3 := (volume : Measure R3).restrict ballOpens
  let d : Lp ℝ 2 muBall := supportedDriftL hcalc 0 beta hbeta K hK hz u
  let principal : R3 → ℝ := fun z => TauCeti.PDE.energyIntegrand (a z) (0 : R3) (0 : ℝ)
    (TauCeti.PDE.jetField u z) (TauCeti.PDE.jetField (v : BallH1) z)
  let driftPairing : R3 → ℝ := fun z => d z * TauCeti.W1p.value (v : BallH1) z
  have hp : Integrable principal muBall :=
    TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u (v : BallH1)
  have hd : Integrable driftPairing muBall :=
    (Lp.memLp d).integrable_mul (Lp.memLp (TauCeti.W1p.value (v : BallH1)))
  have hval : d =ᵐ[muBall]
      fun z => inner ℝ (beta z) (TauCeti.W1p.gradient u z) := by
    simpa only [TauCeti.Wkp.value_zero, TauCeti.Wkp.firstOrder_zero] using
      (supportedDriftL_value_inner_ae hcalc 0 beta hbeta K hK hz u)
  have htotal : TauCeti.PDE.energyFormH1 a beta 0 u (v : BallH1) =
      ∫ z, (principal z + driftPairing z) ∂muBall := by
    rw [TauCeti.PDE.energyFormH1_def]
    apply integral_congr_ae
    filter_upwards [hval] with z hzval
    simp only [principal, driftPairing, Pi.zero_apply,
      TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.jetField_apply,
      TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply, hzval,
      inner_zero_left, zero_mul, add_zero]
  have hprincipal : TauCeti.PDE.energyFormH1 a 0 0 u (v : BallH1) =
      ∫ z, principal z ∂muBall := by
    have hintegrand : (fun z : R3 => TauCeti.PDE.energyIntegrand (a z)
        ((0 : R3 → R3) z) ((0 : R3 → ℝ) z)
        (TauCeti.PDE.jetField u z) (TauCeti.PDE.jetField (v : BallH1) z)) =
          principal := funext fun z => rfl
    exact (TauCeti.PDE.energyFormH1_def (mu := (volume : Measure R3))
      (Omega := ballOpens) a (0 : R3 → R3) (0 : R3 → ℝ) u (v : BallH1)).trans
        (congrArg (fun F : R3 → ℝ => ∫ z, F z ∂muBall) hintegrand)
  have hdrift : TauCeti.PDE.dirichletForcing d v = ∫ z, driftPairing z ∂muBall :=
    TauCeti.PDE.dirichletForcing_apply_eq_setIntegral d v
  exact htotal.trans ((integral_add hp hd).trans
    (congrArg₂ (fun x y : ℝ => x + y) hprincipal.symm hdrift.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
