import Calderon.CoefficientMultiplier
import Calderon.SobolevDivergenceAssembly

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

abbrev SmoothCoefficientMatrix (r : ℕ) := Fin 3 → Fin 3 → SmoothCoefficientJets r

instance instNormedSpaceSmoothCoefficientMatrix (r : ℕ) :
    NormedSpace ℝ (SmoothCoefficientMatrix r) := by
  letI : ∀ _ : Fin 3, SeminormedAddCommGroup (SmoothCoefficientJets r) :=
    fun _ => inferInstance
  letI : ∀ _ : Fin 3, NormedSpace ℝ (SmoothCoefficientJets r) := fun _ => inferInstance
  letI : ∀ _ : Fin 3, SeminormedAddCommGroup (Fin 3 → SmoothCoefficientJets r) :=
    fun _ => inferInstance
  letI : ∀ _ : Fin 3, NormedSpace ℝ (Fin 3 → SmoothCoefficientJets r) :=
    fun _ => Pi.normedSpace (E := fun _ : Fin 3 => SmoothCoefficientJets r)
  exact Pi.normedSpace (E := fun _ : Fin 3 => Fin 3 → SmoothCoefficientJets r)

/-- The actual derivative from the strong subspace before multiplication. -/
def strongCoordinateDerivativeL (hcalc : FixedSobolevCalculus) (s : ℕ) (j : Fin 3) :=
  (unitBallCoordinateDerivativeL hcalc (s + 1) j).comp
    (strongDirichletSubmodule s).toSubmodule.subtypeL

/-- Assemble the actual bounded coefficient multipliers entry by entry. -/
def coefficientMatrixMultiplierL (hcalc : FixedSobolevCalculus) (s : ℕ) :=
  ContinuousLinearMap.pi fun i : Fin 3 => ContinuousLinearMap.pi fun j : Fin 3 =>
    (coefficientMultiplierL hcalc (s + 1)).comp
      ((ContinuousLinearMap.proj j :
        (Fin 3 → SmoothCoefficientJets (s + 2)) →L[ℝ] SmoothCoefficientJets (s + 2)).comp
        (ContinuousLinearMap.proj i :
          SmoothCoefficientMatrix (s + 2) →L[ℝ] Fin 3 → SmoothCoefficientJets (s + 2)))

theorem coefficientMatrixMultiplierL_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (i j : Fin 3) :
    coefficientMatrixMultiplierL hcalc s F i j = coefficientMultiplier hcalc (s + 1) (F i j) :=
  rfl

/-- A bounded linear map into the actual strong-domain operator space. -/
def strongCoefficientOperatorL (hcalc : FixedSobolevCalculus) (s : ℕ) :=
  (unitBallDivergenceL hcalc s).comp (coefficientMatrixMultiplierL hcalc s)

theorem strongCoefficientOperatorL_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) :
    strongCoefficientOperatorL hcalc s F =
      -∑ i, ∑ j, ((unitBallCoordinateDerivativeL hcalc s i).comp
        (coefficientMultiplier hcalc (s + 1) (F i j))).comp
          (strongCoordinateDerivativeL hcalc s j) := by
  exact coefficientDivergenceL_apply _ _ _

theorem strongCoefficientOperatorL_apply_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (u : StrongDirichletSpace s) :
    strongCoefficientOperatorL hcalc s F u =
      -∑ i, ∑ j, unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (strongCoordinateDerivativeL hcalc s j u)) := by
  exact coefficientDivergenceL_apply_apply _ _ _ _

/-- The coefficient bound is fixed before the coefficient matrix. -/
def strongCoefficientOperatorBound (hcalc : FixedSobolevCalculus) (s : ℕ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ‖unitBallCoordinateDerivativeL hcalc s i‖ * sobolevMultiplierBound hcalc (s + 1) *
      ‖strongCoordinateDerivativeL hcalc s j‖

theorem strongCoefficientOperatorBound_nonneg (hcalc : FixedSobolevCalculus) (s : ℕ) :
    0 ≤ strongCoefficientOperatorBound hcalc s :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (sobolevMultiplierBound_nonneg hcalc _))
      (norm_nonneg _)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_strongCoefficientOperator {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : E → SmoothCoefficientMatrix (s + 2)) (q : Set E)
    (hF : ContDiffOn ℝ n F q) :
    ContDiffOn ℝ n (fun x => strongCoefficientOperatorL hcalc s (F x)) q :=
  (strongCoefficientOperatorL hcalc s).contDiff.comp_contDiffOn hF

end OAI.AnisotropicCalderon.DirichletFamily
