import Calderon.PrincipalRegularityBound
import Calderon.SupportedDriftPrincipalRegularity
import Calderon.SupportedDriftRegularityLowerOrder
import Calderon.SupportedDriftRegularityEstimate

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

theorem exists_supportedDrift_regularity_bound_succ
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (s : ℕ)
    (hprevious : ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : BallSobolev s) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a beta 0 (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f) u →
      ∃ V : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s + 1) V = (u : BallH1) ∧
        ‖V‖ ≤ B * (‖u‖ + ‖f‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev (s + 1)) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a beta 0 (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s + 1) f) u →
      ∃ U : BallSobolev (s + 1 + 2),
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s + 1 + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  obtain ⟨B, hB, hprevious⟩ := hprevious
  obtain ⟨c, hc, hregular⟩ := exists_principal_regularity_bound
    (hreg := hreg) (s := s + 1) (a := a) (lam := lam) (Lam := Lam)
    (hsmooth := hsmooth) (hUE := hUE) (hcoeff := hcoeff)
  let D : BallSobolev (s + 1 + 1) →L[ℝ] BallSobolev (s + 1) :=
    supportedDriftL hcalc (s + 1) beta hbeta K hK hz
  refine ⟨c * (2 + ‖D‖ * B), mul_nonneg hc
    (add_nonneg (by norm_num) (mul_nonneg (norm_nonneg D) hB)), ?_⟩
  intro f u hu
  obtain ⟨V, hV, hVbound⟩ := exists_supportedDrift_previous_order_lift
    (s := s) (a := a) (beta := beta) (B := B) (hB := hB)
    (hprevious := hprevious) (f := f) (u := u) (hu := hu)
  obtain ⟨U, hU, hnorm⟩ := exists_supportedDrift_principal_regularity_lift
    (hcalc := hcalc) (s := s + 1) (a := a) (hcoeff := hcoeff) (c := c)
    (hregular := hregular) (beta := beta) (hbeta := hbeta) (K := K) (hK := hK)
    (hz := hz) (f := f) (u := u) (V := V) (hV := hV) (hu := hu)
  refine ⟨U, hU, hnorm.trans ?_⟩
  have hResidual : ‖u‖ + ‖f - D V‖ ≤
      (2 + ‖D‖ * B) * (‖u‖ + ‖f‖) :=
    norm_sub_le_successor_bound
      (E := BallSobolev (s + 1 + 1)) (F := BallSobolev (s + 1))
      (D := D) (V := V) (f := f) (m := ‖u‖) (B := B)
      (hm := norm_nonneg u) (hV := hVbound)
  exact (mul_le_mul_of_nonneg_left hResidual hc).trans
    (mul_assoc c (2 + ‖D‖ * B) (‖u‖ + ‖f‖)).symm.le


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
