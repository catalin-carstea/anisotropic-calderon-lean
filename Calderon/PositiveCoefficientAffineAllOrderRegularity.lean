import Calderon.SmoothPrincipalCorrectionForcing
import Calderon.SmoothPositiveCoefficientNativeCoercivity
import Calderon.NativeZeroTestGreenForcing
import Calderon.FixedDirichletRegularity
import Calderon.TauAffineAlgebra

/-! Actual raw positive coefficient affine solution and derived all-order lifts. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace ContDiff Classical Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def positiveCoefficientDirichletCorrection
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef)
    (f : SmoothData) : BallH1Zero :=
  tauAffineCorrection (mu := (volume : Measure R3)) (Omega := ballOpens) (a := A)
    (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)
    (isCoercive_continuousPositiveCoefficientEnergy A hA.continuous hPos
      (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)) (smoothSobolev f)

def positiveCoefficientDirichletSolution
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef)
    (f : SmoothData) : BallH1 :=
  tauAffineSolution (mu := (volume : Measure R3)) (Omega := ballOpens) (a := A)
    (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)
    (isCoercive_continuousPositiveCoefficientEnergy A hA.continuous hPos
      (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)) (smoothSobolev f)

theorem positiveCoefficientDirichletSolution_weakEquation
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef)
    (f : SmoothData) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 A 0 0 (positiveCoefficientDirichletSolution A hA hPos f)
      (v : BallH1) = 0 :=
  tauAffineSolution_orthogonal (mu := (volume : Measure R3)) (Omega := ballOpens) (a := A)
    (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)
    (isCoercive_continuousPositiveCoefficientEnergy A hA.continuous hPos
      (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)) (smoothSobolev f) v

theorem smoothPrincipalEnergy_eq_cutoffCoefficientEnergy
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (A) 0 0 u v =
      TauCeti.PDE.energyFormH1 (coefficientMatrixField 2 (smoothPrincipalCutoffMatrix 2 A hA))
        0 0 u v := by
  rw [TauCeti.PDE.energyFormH1_def, TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
  rw [coefficientMatrixField_smoothPrincipalCutoffMatrix_eqOn 2 A hA hx]

theorem ordinaryPrincipalL_smoothPrincipal_eq_neg_correctionForcing
    (hcalc : FixedSobolevCalculus) (A : MatrixField) (hA : ContDiff ℝ ∞ A)
    (s : ℕ) (f : SmoothData) :
    TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 (smoothPrincipalCutoffMatrix 2 A hA)
      (smoothBallSobolev 2 f)) =
      -TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f)) := by
  apply Lp.ext
  filter_upwards [ordinaryPrincipalL_smoothPrincipalCutoffMatrix_smooth_value_ae hcalc A hA 0 f,
    Lp.coeFn_neg (TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f))),
    value_smoothBallSobolev_ae s (smoothPrincipalCorrectionForcing A hA f)] with x hx hn hφ
  rw [hx, hn]
  change -(smoothPrincipalCorrectionForcing A hA f).1 x =
    -(TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f)) x)
  exact congrArg (fun t : ℝ => -t) hφ.symm

theorem smoothPrincipalEnergy_smooth_eq_neg_correctionForcing
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (s : ℕ) (f : SmoothData) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (A) 0 0 (smoothSobolev f) (v : BallH1) =
      -TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f))) v := by
  let p : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f))
  have hp : TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0
      (smoothPrincipalCutoffMatrix 2 A hA) (smoothBallSobolev 2 f)) = -p :=
    ordinaryPrincipalL_smoothPrincipal_eq_neg_correctionForcing hcalc A hA s f
  have hE := ordinaryPrincipalL_zero_test_energy_eq_neg_forcing hcalc τ0
    (smoothPrincipalCutoffMatrix 2 A hA) (smoothBallSobolev 2 f) p hp v
  have hFirst : TauCeti.Wkp.firstOrder 1 (smoothBallSobolev 2 f) = smoothSobolev f :=
    firstOrder_smoothBallSobolev 1 f
  have hConvert := congrArg (fun u : BallH1 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (coefficientMatrixField 2 (smoothPrincipalCutoffMatrix 2 A hA)) 0 0 u (v : BallH1)) hFirst
  exact (smoothPrincipalEnergy_eq_cutoffCoefficientEnergy A hA (smoothSobolev f) v).trans
    (hConvert.symm.trans hE)

theorem positiveCoefficientCorrection_smoothForcing_weakEquation
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (s : ℕ) (f : SmoothData) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := A) (b := 0) (c := 0) (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)
      (positiveCoefficientDirichletCorrection A hA hPos f) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f))) v := by
  let z : BallH1Zero := positiveCoefficientDirichletCorrection A hA hPos f
  have hWeak : TauCeti.PDE.energyFormH1 (A) 0 0
      (positiveCoefficientDirichletSolution A hA hPos f) (v : BallH1) = 0 :=
    positiveCoefficientDirichletSolution_weakEquation A hA hPos f v
  have hU : positiveCoefficientDirichletSolution A hA hPos f = smoothSobolev f + (z : BallH1) := rfl
  have hb : (fun x : R3 => (0 : R3)) = (0 : R3 → R3) := rfl
  have hc : (fun x : R3 => (0 : ℝ)) = (0 : R3 → ℝ) := rfl
  have hAdd0 : TauCeti.PDE.energyFormH1 (A)
      (fun x : R3 => (0 : R3)) (fun x : R3 => (0 : ℝ))
      (smoothSobolev f + (z : BallH1)) (v : BallH1) =
      TauCeti.PDE.energyFormH1 (A)
        (fun x : R3 => (0 : R3)) (fun x : R3 => (0 : ℝ)) (smoothSobolev f) (v : BallH1) +
      TauCeti.PDE.energyFormH1 (A)
        (fun x : R3 => (0 : R3)) (fun x : R3 => (0 : ℝ)) (z : BallH1) (v : BallH1) :=
    TauCeti.PDE.energyFormH1_add_left
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := A) (b := fun x : R3 => (0 : R3))
      (c := fun x : R3 => (0 : ℝ))
      (u := smoothSobolev f) (v := (v : BallH1)) (w := (z : BallH1))
      (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)
  have hAdd : TauCeti.PDE.energyFormH1 (A) 0 0
      (smoothSobolev f + (z : BallH1)) (v : BallH1) =
      TauCeti.PDE.energyFormH1 (A) 0 0 (smoothSobolev f) (v : BallH1) +
      TauCeti.PDE.energyFormH1 (A) 0 0 (z : BallH1) (v : BallH1) := by
    simpa only [hb, hc] using hAdd0
  have hTest := (congrArg (fun w : BallH1 => TauCeti.PDE.energyFormH1
    (A) 0 0 w (v : BallH1)) hU).trans hAdd
  have hE := smoothPrincipalEnergy_smooth_eq_neg_correctionForcing hcalc τ0 A hA s f v
  have hZ : TauCeti.PDE.energyFormH1 (A) 0 0 (z : BallH1) (v : BallH1) =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value s (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f))) v := by
    linarith [hTest, hWeak, hE]
  exact (TauCeti.PDE.energyFormH1L0_apply (memLp_continuousCoefficientEnergyIntegrand A hA.continuous) z v).trans hZ

theorem exists_positiveCoefficientDirichletSolution_allOrderLift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (s : ℕ) (f : SmoothData) :
    ∃ U : BallSobolev (s+2),
      TauCeti.Wkp.firstOrder (s+1) U = positiveCoefficientDirichletSolution A hA hPos f := by
  obtain ⟨lam, Lam, hell⟩ := exists_uniformlyEllipticOn_continuousPositiveCoefficient_ball A hA.continuous hPos
  obtain ⟨C, hC, hregular⟩ := hreg s (A) lam Lam
    hA.contDiffOn hell (memLp_continuousCoefficientEnergyIntegrand A hA.continuous)
  let z : BallH1Zero := positiveCoefficientDirichletCorrection A hA hPos f
  obtain ⟨Z, hZ, hNorm⟩ := hregular
    (smoothBallSobolev s (smoothPrincipalCorrectionForcing A hA f)) z
    (fun v => positiveCoefficientCorrection_smoothForcing_weakEquation hcalc τ0 A hA hPos s f v)
  refine ⟨smoothBallSobolev (s+2) f + Z, ?_⟩
  change (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) (s+1)) (smoothBallSobolev (s+2) f + Z) = positiveCoefficientDirichletSolution A hA hPos f
  rw [map_add, TauCeti.Wkp.firstOrderL_apply, firstOrder_smoothBallSobolev,
    TauCeti.Wkp.firstOrderL_apply, hZ]
  rfl

theorem exists_coherent_positiveCoefficientDirichletSolution_allOrderLifts
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData) :
    ∃ U : (s : ℕ) → BallSobolev (s+2),
      (∀ s : ℕ, TauCeti.Wkp.firstOrder (s+1) (U s) = positiveCoefficientDirichletSolution A hA hPos f) ∧
      (∀ s : ℕ, TauCeti.Wkp.lowerOrder (s+2) (U (s+1)) = U s) := by
  choose U hU using (fun s : ℕ => exists_positiveCoefficientDirichletSolution_allOrderLift hcalc hreg τ0 A hA hPos s f)
  refine ⟨U, hU, ?_⟩
  intro s
  apply TauCeti.Wkp.ext (s+2)
  have hV (k : ℕ) : TauCeti.Wkp.value (k+2) (U k) =
      TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) := by
    simpa only [TauCeti.Wkp.value_firstOrder] using
      congrArg (fun w : BallH1 => TauCeti.W1p.value w) (hU k)
  exact (TauCeti.Wkp.value_succ (s+2) (U (s+1))).symm.trans
    ((hV (s+1)).trans (hV s).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.positiveCoefficientDirichletCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.positiveCoefficientDirichletSolution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.positiveCoefficientDirichletSolution_weakEquation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothPrincipalEnergy_eq_cutoffCoefficientEnergy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_smoothPrincipal_eq_neg_correctionForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothPrincipalEnergy_smooth_eq_neg_correctionForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.positiveCoefficientCorrection_smoothForcing_weakEquation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_positiveCoefficientDirichletSolution_allOrderLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_coherent_positiveCoefficientDirichletSolution_allOrderLifts
