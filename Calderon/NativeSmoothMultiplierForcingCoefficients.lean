import Calderon.NativeSmoothMultiplierForcing

/-! Upfront: day-oct13/general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-coefficients-v003.md. Literal principal-gradient and drift-gradient
coefficients of the arbitrary smooth multiplier forcing; no free output bound. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem contDiff_multiplier_gradient_coordinate (Q : SmoothCoefficientJets 3) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 => (gradient (coefficientValue 3 Q) x) i) :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
    ((contDiff_coefficientValue 3 Q).gradient_right (m := ∞) (by simp))

def coefficientWeightedMultiplierGradientJets (r : ℕ) (F : SmoothCoefficientJets r)
    (Q : SmoothCoefficientJets 3) (i : Fin 3) : SmoothCoefficientJets r :=
  compactCoefficient r
    (fun x : R3 => coefficientValue r F x * (gradient (coefficientValue 3 Q) x) i)
    ((contDiff_coefficientValue r F).mul (contDiff_multiplier_gradient_coordinate Q i))
    ((hasCompactSupport_coefficientValue r F).mul_right)

theorem coefficientValue_weightedMultiplierGradientJets (r : ℕ)
    (F : SmoothCoefficientJets r) (Q : SmoothCoefficientJets 3) (i : Fin 3) :
    coefficientValue r (coefficientWeightedMultiplierGradientJets r F Q i) =
      fun x : R3 => coefficientValue r F x * (gradient (coefficientValue 3 Q) x) i :=
  coefficientValue_compactCoefficient r _ _ _

theorem coefficientValue_fin3_sum (r : ℕ) (F : Fin 3 → SmoothCoefficientJets r) :
    coefficientValue r (∑ i : Fin 3, F i) =
      fun x : R3 => ∑ i : Fin 3, coefficientValue r (F i) x := by
  funext x
  simp only [Fin.sum_univ_three, coefficientValue_add, Pi.add_apply]

def smoothMultiplierColumnJets (F : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) (i : Fin 3) : SmoothCoefficientJets 2 :=
  ∑ j : Fin 3, coefficientWeightedMultiplierGradientJets 2 (F i j) Q j

def smoothMultiplierRowJets (F : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) (j : Fin 3) : SmoothCoefficientJets 1 :=
  coefficientFirstJets (∑ i : Fin 3, coefficientWeightedMultiplierGradientJets 2 (F i j) Q i)

def smoothMultiplierDriftJets (G : Fin 3 → SmoothCoefficientJets 1)
    (Q : SmoothCoefficientJets 3) : SmoothCoefficientJets 1 :=
  ∑ i : Fin 3, coefficientWeightedMultiplierGradientJets 1 (G i) Q i

theorem coefficientValue_smoothMultiplierColumnJets (F : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) (i : Fin 3) :
    coefficientValue 2 (smoothMultiplierColumnJets F Q i) =
      fun x : R3 => ∑ j : Fin 3,
        coefficientValue 2 (F i j) x * (gradient (coefficientValue 3 Q) x) j := by
  unfold smoothMultiplierColumnJets
  rw [coefficientValue_fin3_sum]
  simp only [coefficientValue_weightedMultiplierGradientJets]

theorem coefficientValue_smoothMultiplierRowJets (F : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) (j : Fin 3) :
    coefficientValue 1 (smoothMultiplierRowJets F Q j) =
      fun x : R3 => ∑ i : Fin 3,
        coefficientValue 2 (F i j) x * (gradient (coefficientValue 3 Q) x) i := by
  unfold smoothMultiplierRowJets
  rw [coefficientValue_coefficientFirstJets, coefficientValue_fin3_sum]
  simp only [coefficientValue_weightedMultiplierGradientJets]

theorem coefficientValue_smoothMultiplierDriftJets (G : Fin 3 → SmoothCoefficientJets 1)
    (Q : SmoothCoefficientJets 3) :
    coefficientValue 1 (smoothMultiplierDriftJets G Q) =
      fun x : R3 => ∑ i : Fin 3,
        coefficientValue 1 (G i) x * (gradient (coefficientValue 3 Q) x) i := by
  unfold smoothMultiplierDriftJets
  rw [coefficientValue_fin3_sum]
  simp only [coefficientValue_weightedMultiplierGradientJets]

def nativeBulkMultiplierCommutatorForcingL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (G : Fin 3 → SmoothCoefficientJets 1)
    (Q : SmoothCoefficientJets 3) :
    BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  nativeSmoothMultiplierForcingL hcalc (smoothMultiplierColumnJets F Q)
    (smoothMultiplierRowJets F Q) (smoothMultiplierDriftJets G Q)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_multiplier_gradient_coordinate
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientWeightedMultiplierGradientJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_weightedMultiplierGradientJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_fin3_sum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierColumnJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierRowJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierDriftJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_smoothMultiplierColumnJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_smoothMultiplierRowJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_smoothMultiplierDriftJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBulkMultiplierCommutatorForcingL
