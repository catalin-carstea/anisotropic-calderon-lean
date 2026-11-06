import Calderon.MixedKernelConstruction.TaskInterface
import Calderon.MetricOperator
import Calderon.CoordinateBootstrapJets
import Calderon.NormalizedPrincipalMetricSmooth
import Mathlib.Data.Matrix.Basis
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator CoordinateBootstrapJets
open ConformalDepth ActualScalarPrincipalAdjoint ReferenceDensityBounds PrincipalCommutator
open NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
open scoped ContDiff Topology Matrix.Norms.Elementwise

/-- The actual operator associated with one literal coordinate tensor entry. -/
def coordinateMetricOperatorBasis (i j : Fin 3) : R3 →L[ℝ] R3 :=
  matrixOperatorMap (Matrix.single i j (1 : ℝ))

/-- The SAME metric operator is exactly the finite sum of its actual coordinate tensor entries. -/
theorem metricOperatorField_eq_coordinate_sum (h : MatrixField) (x : R3) :
    metricOperatorField h x=∑ i : Fin 3, ∑ j : Fin 3, h x i j • coordinateMetricOperatorBasis i j := by
  have hm : h x=∑ i : Fin 3, ∑ j : Fin 3, h x i j • Matrix.single i j (1 : ℝ) := by
    simpa only [Matrix.smul_single,smul_eq_mul,mul_one] using Matrix.matrix_eq_sum_single (h x)
  change matrixOperatorMap (h x)=_
  conv_lhs => rw [hm]
  simp only [map_sum,map_smul,coordinateMetricOperatorBasis]

/-- Each actual entry's Frechet derivative is controlled by the ORIGINAL first coordinate H8 terms. -/
theorem norm_fderiv_entry_le_coordinateH8 (h : MatrixField) (x : R3) (i j : Fin 3) :
    ‖fderiv ℝ (fun Y => h Y i j) x‖ ≤ 3*coordinateH8 h x := by
  have hDir (k : Fin 3) : |fderiv ℝ (fun Y => h Y i j) x (coordinateDirection k)| ≤ coordinateH8 h x := by
    simpa only [canonicalCoordinatePartial_first,directionalFDeriv] using
      abs_component_partial_le_H8 (firstMultiIndex k) h x (by rw [multiIndexOrder_first];norm_num) i j
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [coordinateH8_nonneg h x])
  intro U
  have hSum : U=∑ k : Fin 3, U k • coordinateDirection k := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr U]
    simp only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,coordinateDirection]
  calc
    ‖fderiv ℝ (fun Y => h Y i j) x U‖ = ‖∑ k : Fin 3, U k • fderiv ℝ (fun Y => h Y i j) x (coordinateDirection k)‖ := by
      conv_lhs => rw [hSum,map_sum]
      simp only [map_smul]
    _ ≤ ∑ k : Fin 3, ‖U k • fderiv ℝ (fun Y => h Y i j) x (coordinateDirection k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 3, ‖U‖*coordinateH8 h x := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le U k) (hDir k)
        (abs_nonneg _) (norm_nonneg U)
    _ = (3*coordinateH8 h x)*‖U‖ := by simp;ring

/-- One universal constant controls actual operator value and first derivative by the SAME coordinate H8. -/
theorem exists_metricOperatorField_first_jet_H8_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : MatrixField),
      (∀ i j, ContDiff ℝ ∞ (fun Y => h Y i j)) → ∀ x : R3,
      ‖metricOperatorField h x‖ ≤ C*coordinateH8 h x ∧
      ‖fderiv ℝ (metricOperatorField h) x‖ ≤ C*coordinateH8 h x := by
  let A : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ‖coordinateMetricOperatorBasis i j‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
  let C : ℝ := 3*(A+1)
  have hC : 0 < C := by dsimp [C];positivity
  have hAC : A ≤ C := by dsimp [C];linarith
  have hA3C : 3*A ≤ C := by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro h hh x
  have hH : 0 ≤ coordinateH8 h x := coordinateH8_nonneg h x
  have hEntry (i j : Fin 3) : |h x i j| ≤ coordinateH8 h x := by
    simpa only [canonicalCoordinatePartial_zero] using
      abs_component_partial_le_H8 zeroMultiIndex h x (by rw [multiIndexOrder_zero];norm_num) i j
  have hValue : ‖metricOperatorField h x‖ ≤ A*coordinateH8 h x := by
    rw [metricOperatorField_eq_coordinate_sum]
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3, h x i j • coordinateMetricOperatorBasis i j‖ ≤
          ∑ i : Fin 3, ∑ j : Fin 3, ‖h x i j • coordinateMetricOperatorBasis i j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, coordinateH8 h x*‖coordinateMetricOperatorBasis i j‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hEntry i j) (norm_nonneg _)
      _ = A*coordinateH8 h x := by simp only [← Finset.mul_sum];dsimp [A];ring
  have hFDij (i j : Fin 3) : HasFDerivAt (fun Y : R3 => h Y i j • coordinateMetricOperatorBasis i j)
      ((fderiv ℝ (fun Y => h Y i j) x).smulRight (coordinateMetricOperatorBasis i j)) x :=
    ((hh i j).differentiable (by simp) x).hasFDerivAt.smul_const (coordinateMetricOperatorBasis i j)
  have hFDrow (i : Fin 3) : HasFDerivAt (fun Y : R3 => ∑ j : Fin 3, h Y i j • coordinateMetricOperatorBasis i j)
      (∑ j : Fin 3, (fderiv ℝ (fun Y => h Y i j) x).smulRight (coordinateMetricOperatorBasis i j)) x :=
    HasFDerivAt.fun_sum (fun j _ => hFDij i j)
  have hFD : HasFDerivAt (fun Y : R3 => ∑ i : Fin 3, ∑ j : Fin 3, h Y i j • coordinateMetricOperatorBasis i j)
      (∑ i : Fin 3, ∑ j : Fin 3, (fderiv ℝ (fun Y => h Y i j) x).smulRight (coordinateMetricOperatorBasis i j)) x :=
    HasFDerivAt.fun_sum (fun i _ => hFDrow i)
  have hFunction : metricOperatorField h=(fun Y => ∑ i : Fin 3, ∑ j : Fin 3, h Y i j • coordinateMetricOperatorBasis i j) :=
    funext (metricOperatorField_eq_coordinate_sum h)
  have hDeriv : ‖fderiv ℝ (metricOperatorField h) x‖ ≤ (3*A)*coordinateH8 h x := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro U
    rw [hFunction,hFD.fderiv]
    simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply]
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3, (fderiv ℝ (fun Y => h Y i j) x) U • coordinateMetricOperatorBasis i j‖ ≤
          ∑ i : Fin 3, ∑ j : Fin 3, ‖(fderiv ℝ (fun Y => h Y i j) x) U • coordinateMetricOperatorBasis i j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ((3*coordinateH8 h x)*‖U‖)*‖coordinateMetricOperatorBasis i j‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul,Real.norm_eq_abs]
        have hEval : |(fderiv ℝ (fun Y => h Y i j) x) U| ≤ ‖fderiv ℝ (fun Y => h Y i j) x‖*‖U‖ := by
          simpa only [Real.norm_eq_abs] using (fderiv ℝ (fun Y => h Y i j) x).le_opNorm U
        exact mul_le_mul_of_nonneg_right
          (hEval.trans (mul_le_mul_of_nonneg_right (norm_fderiv_entry_le_coordinateH8 h x i j) (norm_nonneg U))) (norm_nonneg _)
      _ = ((3*A)*coordinateH8 h x)*‖U‖ := by simp only [← Finset.mul_sum];dsimp [A];ring
  exact ⟨hValue.trans (mul_le_mul_of_nonneg_right hAC hH),hDeriv.trans (mul_le_mul_of_nonneg_right hA3C hH)⟩

/-- The ORIGINAL current bootstrap controls both jets of the ACTUAL normalized principal perturbation. -/
theorem exists_current_normalized_principal_operator_jet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : KnownSideSourceData) (L lam delta Rstar eps : ℝ) (p : ℕ),
      CurrentRadiusBootstrap S L lam delta Rstar eps p → ∀ y ∈ cylinder,
      ‖metricOperatorField (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y‖ ≤
        C*(eps*referenceRadius delta Rstar p L y) ∧
      ‖fderiv ℝ (metricOperatorField (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam)) y‖ ≤
        C*(eps*referenceRadius delta Rstar p L y) := by
  obtain ⟨C,hC,HC⟩ := exists_metricOperatorField_first_jet_H8_bound
  refine ⟨C,hC,?_⟩
  intro S L lam delta Rstar eps p hBoot y hy
  have hSmooth := contDiff_referenceNormalizedPrincipalDifference_entry S.g1 S.g2 S.g1_admissible S.g2_admissible L lam
  have hh := HC (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) hSmooth y
  have hB := mul_le_mul_of_nonneg_left (hBoot.1 y hy) hC.le
  exact ⟨hh.1.trans hB,hh.2.trans hB⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
