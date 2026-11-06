import Calderon.CoefficientJetSpace
import Calderon.FixedSobolevCalculus

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Function
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- One multiplier constant is selected before all coefficients and inputs. -/
def sobolevMultiplierBound (hcalc : FixedSobolevCalculus) (k : ℕ) : ℝ :=
  Classical.choose (hcalc.1 k)

theorem sobolevMultiplierBound_nonneg (hcalc : FixedSobolevCalculus) (k : ℕ) :
    0 ≤ sobolevMultiplierBound hcalc k :=
  (Classical.choose_spec (hcalc.1 k)).1

theorem exists_coefficientMultiplier (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k + 1)) :
    ∃ T : BallSobolev k →L[ℝ] BallSobolev k,
      (∀ f : BallSobolev k,
        TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k (T f)
          =ᵐ[((volume : Measure R3).restrict ballOpens)]
          fun x => coefficientValue (k + 1) F x * TauCeti.Wkp.value
            (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k f x) ∧
      ‖T‖ ≤ sobolevMultiplierBound hcalc k * ‖F‖ := by
  exact (Classical.choose_spec (hcalc.1 k)).2
    (coefficientValue (k + 1) F) (contDiff_coefficientValue _ F)
    (hasCompactSupport_coefficientValue _ F) ‖F‖ (norm_nonneg F)
    (fun j hj x => norm_iteratedFDeriv_coefficientValue_le _ F j hj x)

/-- Multiplication by the actual coefficient, with its full value specification. -/
def coefficientMultiplier (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k + 1)) :=
  Classical.choose (exists_coefficientMultiplier hcalc k F)

theorem coefficientMultiplier_value_ae (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k + 1)) (f : BallSobolev k) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k
      (coefficientMultiplier hcalc k F f)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue (k + 1) F x * TauCeti.Wkp.value
        (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k f x :=
  (Classical.choose_spec (exists_coefficientMultiplier hcalc k F)).1 f

theorem norm_coefficientMultiplier_le (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k + 1)) :
    ‖coefficientMultiplier hcalc k F‖ ≤ sobolevMultiplierBound hcalc k * ‖F‖ :=
  (Classical.choose_spec (exists_coefficientMultiplier hcalc k F)).2

theorem coefficientMultiplier_add (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F G : SmoothCoefficientJets (k + 1)) :
    coefficientMultiplier hcalc k (F + G) =
      coefficientMultiplier hcalc k F + coefficientMultiplier hcalc k G := by
  apply ContinuousLinearMap.ext
  intro f
  apply TauCeti.Wkp.ext k
  rw [add_apply, TauCeti.Wkp.value_add]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k (F + G) f,
    coefficientMultiplier_value_ae hcalc k F f,
    coefficientMultiplier_value_ae hcalc k G f,
    Lp.coeFn_add (TauCeti.Wkp.value k (coefficientMultiplier hcalc k F f))
      (TauCeti.Wkp.value k (coefficientMultiplier hcalc k G f))] with x hFG hF hG hadd
  rw [hFG, hadd]
  simp only [Pi.add_apply]
  rw [hF, hG]
  rw [coefficientValue_add]
  simp only [Pi.add_apply, add_mul]

theorem coefficientMultiplier_smul (hcalc : FixedSobolevCalculus) (k : ℕ)
    (c : ℝ) (F : SmoothCoefficientJets (k + 1)) :
    coefficientMultiplier hcalc k (c • F) = c • coefficientMultiplier hcalc k F := by
  apply ContinuousLinearMap.ext
  intro f
  apply TauCeti.Wkp.ext k
  rw [smul_apply, TauCeti.Wkp.value_smul]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k (c • F) f,
    coefficientMultiplier_value_ae hcalc k F f,
    Lp.coeFn_smul c (TauCeti.Wkp.value k (coefficientMultiplier hcalc k F f))]
      with x hcF hF hsmul
  rw [hcF, hsmul]
  simp only [Pi.smul_apply]
  rw [hF, coefficientValue_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Linearity follows from injectivity of actual Sobolev values. -/
def coefficientMultiplierLinearMap (hcalc : FixedSobolevCalculus) (k : ℕ) :
    SmoothCoefficientJets (k + 1) →ₗ[ℝ] BallSobolev k →L[ℝ] BallSobolev k where
  toFun := coefficientMultiplier hcalc k
  map_add' := coefficientMultiplier_add hcalc k
  map_smul' := coefficientMultiplier_smul hcalc k

/-- The actual coefficient-to-operator map is bounded with one fixed constant. -/
def coefficientMultiplierL (hcalc : FixedSobolevCalculus) (k : ℕ) :=
  (coefficientMultiplierLinearMap hcalc k).mkContinuous (sobolevMultiplierBound hcalc k)
    (norm_coefficientMultiplier_le hcalc k)

theorem coefficientMultiplierL_apply (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k + 1)) :
    coefficientMultiplierL hcalc k F = coefficientMultiplier hcalc k F := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_coefficientMultiplier {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : E → SmoothCoefficientJets (k + 1)) (s : Set E)
    (hF : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun x => coefficientMultiplierL hcalc k (F x)) s :=
  (coefficientMultiplierL hcalc k).contDiff.comp_contDiffOn hF

end OAI.AnisotropicCalderon.DirichletFamily
