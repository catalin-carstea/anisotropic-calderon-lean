import Calderon.OrdinaryWeightedDriftOperator

/-! Expanded first in EXPANSION-actual-rotation-strong-zero-room-lift-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma coefficientMultiplier_eq_smul_of_value_eq
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F G : SmoothCoefficientJets (k+1))
    (c : ℝ) (hFG : ∀ x, coefficientValue (k+1) F x = c * coefficientValue (k+1) G x) :
    coefficientMultiplier hcalc k F = c • coefficientMultiplier hcalc k G := by
  apply ContinuousLinearMap.ext
  intro u
  apply TauCeti.Wkp.ext k
  rw [ContinuousLinearMap.smul_apply,TauCeti.Wkp.value_smul]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F u,
    coefficientMultiplier_value_ae hcalc k G u,
    Lp.coeFn_smul c (TauCeti.Wkp.value k (coefficientMultiplier hcalc k G u))] with x hF hG hs
  rw [hF,hs]
  change coefficientValue (k+1) F x * TauCeti.Wkp.value k u x =
    c * TauCeti.Wkp.value k (coefficientMultiplier hcalc k G u) x
  rw [hG,hFG]
  exact mul_assoc _ _ _

lemma ordinaryPrincipalL_eq_of_coefficientMatrixField_eq
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F G : SmoothCoefficientMatrix (s+2))
    (hFG : coefficientMatrixField (s+2) F = coefficientMatrixField (s+2) G) :
    ordinaryPrincipalL hcalc s F = ordinaryPrincipalL hcalc s G := by
  have hm (i j : Fin 3) : coefficientMultiplier hcalc (s+1) (F i j) =
      coefficientMultiplier hcalc (s+1) (G i j) := by
    have h := coefficientMultiplier_eq_smul_of_value_eq hcalc (s+1) (F i j) (G i j) 1
      (fun x => by simpa only [one_mul,coefficientMatrixField] using congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) (congr_fun hFG x))
    simpa only [one_smul] using h
  apply ContinuousLinearMap.ext
  intro U
  rw [ordinaryPrincipalL_apply,ordinaryPrincipalL_apply]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (unitBallCoordinateDerivativeL hcalc s i)
    (congrArg (fun T : BallSobolev (s+1) →L[ℝ] BallSobolev (s+1) =>
      T (unitBallCoordinateDerivativeL hcalc (s+1) j U)) (hm i j))

lemma sum_fullWeightedDriftMultipliers_eq_ordinaryWeightedDriftL
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → w (p,x) = 0)
    (L : ℝ) (p : R3 × ℝ) (G : Fin 3 → SmoothCoefficientJets (s+1))
    (hG : ∀ j x, coefficientValue (s+1) (G j) x = weightedDriftSlice w b L p x j) :
    (∑ j : Fin 3, (coefficientMultiplier hcalc s (G j)).comp
      (ordinaryLowerOrderCoordinateDerivativeL hcalc s j)) =
    ordinaryWeightedDriftL hcalc s w hw b hb K hK hz L p := by
  have hm (j : Fin 3) : coefficientMultiplier hcalc s (G j) =
      (-L*p.2) • coefficientMultiplier hcalc s
        (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b j)
          (contDiff_weightedDriftCoordinate w hw b hb j) K hK
          (weightedDriftCoordinate_support w b K hz j) p) := by
    apply coefficientMultiplier_eq_smul_of_value_eq
    intro x
    rw [hG,coefficientValue_commonSupportCoefficientFamily]
    simp only [weightedDriftSlice,weightedLinearRadialDrift,weightedDriftCoordinate,
      PiLp.smul_apply,smul_eq_mul]
  apply ContinuousLinearMap.ext
  intro U
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,hm,
    ContinuousLinearMap.smul_apply,ordinaryWeightedDriftL,ordinaryWeightedDriftBaseL,Finset.smul_sum]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMultiplier_eq_smul_of_value_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_eq_of_coefficientMatrixField_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_fullWeightedDriftMultipliers_eq_ordinaryWeightedDriftL
