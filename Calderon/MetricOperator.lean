import Calderon.MetricInverse
import Calderon.GeodesicFlow
import OAI.Analysis.AnisotropicCalderon.Defs
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic

set_option maxSynthPendingDepth 10
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError

noncomputable def matrixOperatorAlgEquiv :
    Matrix (Fin 3) (Fin 3) ℝ ≃ₐ[ℝ] (R3 →L[ℝ] R3) :=
  (Matrix.toLpLinAlgEquiv 2 : Matrix (Fin 3) (Fin 3) ℝ ≃ₐ[ℝ] Module.End ℝ R3).trans
    (Module.End.toContinuousLinearMap R3)

noncomputable def matrixOperatorMap :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] R3 →L[ℝ] R3 :=
  matrixOperatorAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def metricOperatorField (g : MatrixField) : R3 → R3 →L[ℝ] R3 :=
  fun x => matrixOperatorMap (g x)

theorem metricOperatorField_apply (g : MatrixField) (x X : R3) :
    metricOperatorField g x X = (g x).toEuclideanLin X := rfl

theorem contDiff_metricOperatorField (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (metricOperatorField g) := by
  have hs : ContDiff ℝ ∞ g :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => hg.smooth i j))
  exact matrixOperatorMap.contDiff.comp hs

theorem isUnit_metricOperatorField (g : MatrixField) (hg : IsAdmissibleMetric g) (x : R3) :
    IsUnit (metricOperatorField g x) :=
  (hg.posDef x).isUnit.map matrixOperatorAlgEquiv.toMonoidHom

theorem metricOperatorField_symmetric (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x X Z : R3) :
    inner ℝ (metricOperatorField g x X) Z = inner ℝ (metricOperatorField g x Z) X := by
  change inner ℝ ((g x).toEuclideanLin X) Z = inner ℝ ((g x).toEuclideanLin Z) X
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hg.posDef x).isHermitian
  exact (hs X Z).trans (real_inner_comm _ _)

theorem metricOperatorField_derivative_symmetric (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x U X Z : R3) :
    inner ℝ (fderiv ℝ (metricOperatorField g) x U X) Z =
      inner ℝ (fderiv ℝ (metricOperatorField g) x U Z) X :=
  inverse_metric_derivative_symmetric _ _ x
    (((contDiff_infty_iff_fderiv.mp (contDiff_metricOperatorField g hg)).1 x).hasFDerivAt)
    (Filter.Eventually.of_forall (fun y => metricOperatorField_symmetric g hg y)) U X Z

theorem inverseMetricField_eq_matrix_inverse (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x : R3) :
    inverseMetricField (metricOperatorField g) x = matrixOperatorMap ((g x)⁻¹) := by
  obtain ⟨u,hu⟩ := (hg.posDef x).isUnit
  change Ring.inverse (matrixOperatorAlgEquiv (g x)) = matrixOperatorAlgEquiv ((g x)⁻¹)
  rw [← hu,Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_unit]
  change Ring.inverse ((Units.map matrixOperatorAlgEquiv.toMonoidHom u).val) =
    ((Units.map matrixOperatorAlgEquiv.toMonoidHom u)⁻¹).val
  rw [Ring.inverse_unit]

theorem contDiff_metricCoordinateConnection (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (coordinateConnectionField
      (inverseMetricField (metricOperatorField g)) (metricOperatorField g)) :=
  contDiff_coordinateConnectionField_infty _ _
    (contDiff_inverseMetricField _ (contDiff_metricOperatorField g hg)
      (isUnit_metricOperatorField g hg)) (contDiff_metricOperatorField g hg)

theorem metricCoordinateConnection_symmetric (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x X Y : R3) :
    coordinateConnectionField (inverseMetricField (metricOperatorField g))
      (metricOperatorField g) x X Y =
    coordinateConnectionField (inverseMetricField (metricOperatorField g))
      (metricOperatorField g) x Y X := by
  simp only [coordinateConnectionField_apply]
  exact coordinateConnection_symmetric _ _
    (metricOperatorField_derivative_symmetric g hg x) X Y

theorem metricCoordinateConnection_koszul (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x X Y Z : R3) :
    2*inner ℝ (metricOperatorField g x
      (coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x X Y)) Z =
      inner ℝ (fderiv ℝ (metricOperatorField g) x X Y) Z +
      inner ℝ (fderiv ℝ (metricOperatorField g) x Y X) Z -
      inner ℝ (fderiv ℝ (metricOperatorField g) x Z X) Y := by
  rw [coordinateConnectionField_apply]
  exact coordinateConnection_koszul _ _ _
    (fun V => metric_apply_inverseMetricField _ (isUnit_metricOperatorField g hg) x V) X Y Z

theorem metricCoordinateConnection_metric_compatible (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x X Y Z : R3) :
    inner ℝ (metricOperatorField g x
      (coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x X Y)) Z +
    inner ℝ (metricOperatorField g x Y)
      (coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x X Z) =
      inner ℝ (fderiv ℝ (metricOperatorField g) x X Y) Z := by
  have h1 := metricCoordinateConnection_koszul g hg x X Y Z
  have h2 := metricCoordinateConnection_koszul g hg x X Z Y
  have hsym := metricOperatorField_symmetric g hg x Y
    (coordinateConnectionField (inverseMetricField (metricOperatorField g))
      (metricOperatorField g) x X Z)
  have hderiv := metricOperatorField_derivative_symmetric g hg x X Y Z
  nlinarith

theorem exists_metricConnection_bounds_on_compact (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x ∈ K,
      ‖coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x‖ ≤ C ∧
      ‖fderiv ℝ (coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g)) x‖ ≤ D :=
  exists_connection_bounds_on_compact _ _
    (contDiff_inverseMetricField _ (contDiff_metricOperatorField g hg)
      (isUnit_metricOperatorField g hg)) (contDiff_metricOperatorField g hg) K hK

theorem exists_local_metric_geodesic (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x₀ v₀ : R3) (t₀ : ℝ) :
    ∃ a > (0:ℝ), ∃ ε > (0:ℝ), ∀ z ∈ Metric.closedBall (x₀,v₀) a,
      ∃ q v : ℝ → R3, q t₀ = z.1 ∧ v t₀ = z.2 ∧
        ∀ t ∈ Set.Ioo (t₀-ε) (t₀+ε),
          HasDerivAt q (v t) t ∧
          HasDerivAt v (-coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g)
            (q t) (v t) (v t)) t :=
  exists_local_coordinate_geodesic _ _
    (contDiff_inverseMetricField _ (contDiff_metricOperatorField g hg)
      (isUnit_metricOperatorField g hg)) (contDiff_metricOperatorField g hg) x₀ v₀ t₀

theorem hasDerivAt_metric_geodesic_energy_zero (g : MatrixField)
    (hg : IsAdmissibleMetric g) (q v : ℝ → R3) (t : ℝ)
    (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (-coordinateConnectionField
      (inverseMetricField (metricOperatorField g)) (metricOperatorField g)
      (q t) (v t) (v t)) t) :
    HasDerivAt (fun s => inner ℝ (metricOperatorField g (q s) (v s)) (v s)) 0 t := by
  have hM := ((contDiff_infty_iff_fderiv.mp
    (contDiff_metricOperatorField g hg)).1 (q t)).hasFDerivAt
  have he := ((hM.comp_hasDerivAt t hq).clm_apply hv).inner ℝ hv
  let A := coordinateConnectionField (inverseMetricField (metricOperatorField g))
    (metricOperatorField g) (q t) (v t) (v t)
  have hzero : inner ℝ (metricOperatorField g (q t) (v t)) (-A) +
      inner ℝ (fderiv ℝ (metricOperatorField g) (q t) (v t) (v t) +
        metricOperatorField g (q t) (-A)) (v t) = 0 := by
    have hc := metricCoordinateConnection_metric_compatible g hg (q t) (v t) (v t) (v t)
    change inner ℝ (metricOperatorField g (q t) A) (v t) +
      inner ℝ (metricOperatorField g (q t) (v t)) A =
      inner ℝ (fderiv ℝ (metricOperatorField g) (q t) (v t) (v t)) (v t) at hc
    simp only [map_neg,inner_neg_right,inner_add_left,inner_neg_left]
    linarith
  change HasDerivAt (fun s => inner ℝ (metricOperatorField g (q s) (v s)) (v s))
    (inner ℝ (metricOperatorField g (q t) (v t)) (-A) +
      inner ℝ (fderiv ℝ (metricOperatorField g) (q t) (v t) (v t) +
        metricOperatorField g (q t) (-A)) (v t)) t at he
  rw [hzero] at he
  exact he

#print axioms hasDerivAt_metric_geodesic_energy_zero
#print axioms contDiff_metricOperatorField
#print axioms inverseMetricField_eq_matrix_inverse
#print axioms exists_metricConnection_bounds_on_compact
#print axioms metricCoordinateConnection_symmetric
#print axioms metricCoordinateConnection_metric_compatible
#print axioms exists_local_metric_geodesic
end OAI.AnisotropicCalderon.MetricOperator
