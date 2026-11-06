import Calderon.SupportedDriftPrincipalRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_supportedDrift_regularity_bound_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev 0) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet a beta 0 (TauCeti.Wkp.value 0 f) u →
      ∃ U : BallSobolev (0 + 2),
        TauCeti.Wkp.firstOrder (0 + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  obtain ⟨c, hc, hregular⟩ := hreg 0 a lam Lam hsmooth hUE hcoeff
  let D := supportedDriftL hcalc 0 beta hbeta K hK hz
  refine ⟨c * (1 + ‖D‖), mul_nonneg hc (by positivity), ?_⟩
  intro f u hu
  let r : BallSobolev 0 := f - D (u : BallH1)
  have hlift := exists_supportedDrift_principal_regularity_lift
    (hcalc := hcalc) (s := 0) (a := a) (hcoeff := hcoeff) (c := c)
    (hregular := hregular) (beta := beta) (hbeta := hbeta) (K := K) (hK := hK)
    (hz := hz) (f := f) (u := u) (V := (u : BallH1))
    (hV := TauCeti.Wkp.firstOrder_zero (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) (u : BallH1)) (hu := hu)
  obtain ⟨U, hU, hnorm⟩ := hlift
  refine ⟨U, hU, hnorm.trans ?_⟩
  have hD : ‖D (u : BallH1)‖ ≤ ‖D‖ * ‖u‖ := D.le_opNorm (u : BallH1)
  calc
    c * (‖u‖ + ‖r‖) ≤ c * (‖u‖ + (‖f‖ + ‖D (u : BallH1)‖)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_refl ‖u‖) (norm_sub_le f (D (u : BallH1)))) hc
    _ ≤ c * (‖u‖ + (‖f‖ + ‖D‖ * ‖u‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖u‖) (add_le_add (le_refl ‖f‖) hD)) hc
    _ ≤ c * ((1 + ‖D‖) * (‖u‖ + ‖f‖)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (norm_nonneg D) (norm_nonneg f)]) hc
    _ = _ := by ring


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
