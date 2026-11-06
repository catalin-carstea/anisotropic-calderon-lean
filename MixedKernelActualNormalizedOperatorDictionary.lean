import MixedKernelCurrentH8OperatorJet
import Calderon.ConformalReferenceOperators
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator ConformalDepth
open NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
open scoped ContDiff Topology

/-- The genuine inverse at a positive matrix is preserved by the actual matrix/operator algebra equivalence. -/
theorem matrixOperatorMap_inverse_of_posDef
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) :
    Ring.inverse (matrixOperatorMap A)=matrixOperatorMap A⁻¹ := by
  obtain ⟨u,hu⟩ := hA.isUnit
  change Ring.inverse (matrixOperatorAlgEquiv A)=matrixOperatorAlgEquiv A⁻¹
  rw [← hu,Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_unit]
  change Ring.inverse ((Units.map matrixOperatorAlgEquiv.toMonoidHom u).val)=
    ((Units.map matrixOperatorAlgEquiv.toMonoidHom u)⁻¹).val
  rw [Ring.inverse_unit]

/-- The two original reference metric definitions coincide with their EXACT exponent/depth convention. -/
theorem referenceMetric_eq_conformalReferenceMatrix (g : MatrixField) (L lam : ℝ) :
    referenceMetric (dilatedMetric g lam) L=conformalReferenceMatrix g L lam := by
  funext y
  dsimp [referenceMetric,EnergyBridge.conformalMatrix,dilatedMetric,conformalReferenceMatrix]
  have he : 2*(-L*referenceCoordinateDepth y) = -2*L*conformalReferenceCoordinateDepth y := by
    unfold referenceCoordinateDepth conformalReferenceCoordinateDepth
    ring
  rw [he]

/-- The ORIGINAL H8 tensor is exactly the difference of the actual principal operators. -/
theorem normalized_principal_operator_difference_eq
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3) :
    metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) y-
      Ring.inverse (metricOperatorField (conformalReferenceMatrix S.g1 L lam) y)=
      metricOperatorField (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y := by
  have hPos : (conformalReferenceMatrix S.g1 L lam y).PosDef := by
    rw [← referenceMetric_eq_conformalReferenceMatrix S.g1 L lam]
    exact EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) y
  change matrixOperatorMap (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam y)-
    Ring.inverse (matrixOperatorMap (conformalReferenceMatrix S.g1 L lam y))=matrixOperatorMap _
  rw [matrixOperatorMap_inverse_of_posDef _ hPos]
  rw [← referenceMetric_eq_conformalReferenceMatrix S.g1 L lam]
  change matrixOperatorMap (normalizedPrincipalMatrix _ _)-matrixOperatorMap _=
    matrixOperatorMap (normalizedPrincipalMatrix _ _- _)
  rw [map_sub]

/-- The ACTUAL normalized principal operator is a unit, from the original positive-definite metrics. -/
theorem isUnit_normalized_principal_operator
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3) :
    IsUnit (metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) y) := by
  change IsUnit (matrixOperatorAlgEquiv (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam y))
  exact (normalizedPrincipalMatrix_posDef _ _
    (EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) y)
    (dilatedMetric_posDef S.g2 S.g2_admissible lam y)).isUnit.map matrixOperatorAlgEquiv.toMonoidHom

/-- Its genuine inverse is EXACTLY the covariant second metric used by the original geometric test. -/
theorem actual_covariant_second_operator_eq_ringInverse
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3) :
    metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹) y=
      Ring.inverse (metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) y) := by
  exact (matrixOperatorMap_inverse_of_posDef _ (normalizedPrincipalMatrix_posDef _ _
    (EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) y)
    (dilatedMetric_posDef S.g2 S.g2_admissible lam y))).symm

/-- Smooth scalar tensor entries give the actual globally smooth operator field, without exterior admissibility. -/
theorem contDiff_metricOperatorField_of_entries (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun Y => h Y i j)) : ContDiff ℝ ∞ (metricOperatorField h) := by
  have heq : metricOperatorField h=(fun Y => ∑ i : Fin 3, ∑ j : Fin 3, h Y i j • coordinateMetricOperatorBasis i j) :=
    funext (metricOperatorField_eq_coordinate_sum h)
  rw [heq]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (hh i j).smul_const (coordinateMetricOperatorBasis i j)))

theorem contDiff_actual_normalized_principal_operator
    (S : KnownSideSourceData) (L lam : ℝ) :
    ContDiff ℝ ∞ (metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam)) := by
  apply contDiff_metricOperatorField_of_entries
  intro i j
  have hj := contDiff_referenceNormalizedPrincipalMatrix_entry_joint S.g1 S.g2 S.g1_admissible S.g2_admissible L i j
  simpa only [Function.comp_def,id_eq] using hj.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_actual_covariant_second_operator
    (S : KnownSideSourceData) (L lam : ℝ) :
    ContDiff ℝ ∞ (metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)) := by
  have heq : metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)=
      (fun Y => Ring.inverse (metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) Y)) :=
    funext (actual_covariant_second_operator_eq_ringInverse S L lam)
  rw [heq]
  exact contDiff_actual_operatorRingInverse _ (contDiff_actual_normalized_principal_operator S L lam)
    (isUnit_normalized_principal_operator S L lam)

/-- The inverse metric field in the original second connection is the SAME actual principal operator. -/
theorem inverse_actual_covariant_second_operator_eq_principal
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3) :
    inverseMetricField (metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)) y=
      metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam) y := by
  change Ring.inverse (metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹) y)=_
  rw [actual_covariant_second_operator_eq_ringInverse]
  obtain ⟨u,hu⟩ := isUnit_normalized_principal_operator S L lam y
  rw [← hu,Ring.inverse_unit,Ring.inverse_unit]
  rfl

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
