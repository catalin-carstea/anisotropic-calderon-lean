import Calderon.ActualFrameParallelVelocity
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Actual conformal Gram frame, canonical connection coefficients, and the
negative parallel angular velocity on the same unit sphere. Source-only proposal. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology InnerProductSpace Manifold EuclideanSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame

private instance instCompleteGramAngularR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

def conformalReferenceGramFrame (g : MatrixField) (L : ℝ)
    (p : ℝ × R3) : Fin 3 → R3 :=
  NormalCoordinatesFrame.metricGramFrame (conformalReferenceOperatorJoint g L p)

def conformalReferenceFrameConnectionCoefficient (g : MatrixField) (L q : ℝ)
    (y X : R3) : Fin 3 → Fin 3 → ℝ :=
  MovingFrameConnection.frameConnectionCoefficient
    (metricOperatorField (conformalReferenceMatrix g L q))
    (coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q)))
    (fun x => conformalReferenceGramFrame g L (q,x)) y X

def conformalReferenceParallelAngularVelocity (g : MatrixField) (L q : ℝ)
    (y X z : R3) : R3 :=
  framedParallelAngularVelocity
    (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
    (coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))) y X z

theorem conformalReferenceGramFrameOperatorJoint_eq_frameOperator
    (g : MatrixField) (L : ℝ) (p : ℝ × R3) :
    conformalReferenceGramFrameOperatorJoint g L p =
      NormalCoordinatesFrame.frameOperator (conformalReferenceGramFrame g L p) := rfl

theorem conformalReferenceGramFrame_isMetricOrthonormalFrame
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (p : ℝ × R3) :
    NormalCoordinatesFrame.IsMetricOrthonormalFrame
      (conformalReferenceOperatorJoint g L p) (conformalReferenceGramFrame g L p) := by
  exact NormalCoordinatesFrame.metricGramFrame_isMetricOrthonormalFrame _
    (conformalReferenceOperatorJoint_symmetric g hg L p)
    (conformalReferenceOperatorJoint_pos g hg L p)

theorem contDiff_conformalReferenceGramFrame
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 => conformalReferenceGramFrame g L p i) := by
  exact NormalCoordinatesFrame.contDiff_metricGramFrame _
    (contDiff_conformalReferenceOperatorJoint g hg L)
    (conformalReferenceOperatorJoint_pos g hg L) i

theorem conformalReferenceCoordinateConnection_metric_compatible
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (y X U V : R3) :
    inner ℝ
      (metricOperatorField (conformalReferenceMatrix g L q) y
        (coordinateConnectionField
          (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
          (metricOperatorField (conformalReferenceMatrix g L q)) y X U)) V +
      inner ℝ (metricOperatorField (conformalReferenceMatrix g L q) y U)
        (coordinateConnectionField
          (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
          (metricOperatorField (conformalReferenceMatrix g L q)) y X V) =
      inner ℝ (fderiv ℝ (metricOperatorField (conformalReferenceMatrix g L q)) y X U) V := by
  let M : R3 → R3 →L[ℝ] R3 := metricOperatorField (conformalReferenceMatrix g L q)
  have hD := conformalReference_slice_data g hg L q
  have hunit : ∀ x, IsUnit (M x) := fun x =>
    isUnit_of_strictly_positive (M x) (conformalReferenceOperatorJoint_pos g hg L (q,x))
  exact CurvatureSkew.coordinateConnectionField_metric_compatible M hD.1 hunit
    hD.2.2.1 y X U V

theorem conformalReferenceFrameConnectionCoefficient_skew
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (y X : R3) (a b : Fin 3) :
    conformalReferenceFrameConnectionCoefficient g L q y X a b =
      -conformalReferenceFrameConnectionCoefficient g L q y X b a := by
  let M : R3 → R3 →L[ℝ] R3 := metricOperatorField (conformalReferenceMatrix g L q)
  let Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3 := coordinateConnectionField (inverseMetricField M) M
  let e : R3 → Fin 3 → R3 := fun x => conformalReferenceGramFrame g L (q,x)
  have hD := conformalReference_slice_data g hg L q
  have hE : ∀ i, ContDiff ℝ ∞ (fun x => e x i) := by
    intro i
    exact (contDiff_conformalReferenceGramFrame g hg L i).comp
      (contDiff_const.prodMk contDiff_id)
  have he : ∀ x, RadiusProfile.IsMetricOrthonormalFrame (M x) (e x) := by
    intro x
    change NormalCoordinatesFrame.IsMetricOrthonormalFrame
      (conformalReferenceOperatorJoint g L (q,x)) (conformalReferenceGramFrame g L (q,x))
    exact conformalReferenceGramFrame_isMetricOrthonormalFrame g hg L (q,x)
  have hcomp : ∀ x X U V, inner ℝ (M x (Γ x X U)) V +
      inner ℝ (M x U) (Γ x X V) = inner ℝ (fderiv ℝ M x X U) V := by
    intro x X U V
    exact conformalReferenceCoordinateConnection_metric_compatible g hg L q x X U V
  exact MovingFrameConnection.frameConnectionCoefficient_skew M Γ e hD.1 hE
    hD.2.2.1 he hcomp y X a b

theorem conformalReferenceParallelAngularVelocity_frame_component
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (y X : R3) (a b : Fin 3) :
    inner ℝ
      (conformalReferenceParallelAngularVelocity g L q y X
        (NormalCoordinatesFrame.coordinateVector b))
      (NormalCoordinatesFrame.coordinateVector a) =
      -conformalReferenceFrameConnectionCoefficient g L q y X a b := by
  let M : R3 → R3 →L[ℝ] R3 := metricOperatorField (conformalReferenceMatrix g L q)
  let Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3 := coordinateConnectionField (inverseMetricField M) M
  let e : R3 → Fin 3 → R3 := fun x => conformalReferenceGramFrame g L (q,x)
  have hF : ContDiff ℝ ∞ (fun x => NormalCoordinatesFrame.frameOperator (e x)) := by
    change ContDiff ℝ ∞ (fun x : R3 => conformalReferenceGramFrameOperatorJoint g L (q,x))
    exact (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
      (contDiff_const.prodMk contDiff_id)
  have he : NormalCoordinatesFrame.IsMetricOrthonormalFrame (M y) (e y) :=
    conformalReferenceGramFrame_isMetricOrthonormalFrame g hg L (q,y)
  exact framedParallelAngularVelocity_frame_component M Γ e hF y X he a b

theorem gramAngular_sum_coordinateVector (z : R3) :
    (∑ b : Fin 3, z b • NormalCoordinatesFrame.coordinateVector b) = z := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,
    NormalCoordinatesFrame.coordinateVector] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr z

theorem conformalReferenceParallelAngularVelocity_sum_coordinates
    (g : MatrixField) (L q : ℝ) (y X z : R3) :
    conformalReferenceParallelAngularVelocity g L q y X z =
      ∑ b : Fin 3, z b • conformalReferenceParallelAngularVelocity g L q y X
        (NormalCoordinatesFrame.coordinateVector b) := by
  let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
  let Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3 := coordinateConnectionField
    (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
    (metricOperatorField (conformalReferenceMatrix g L q))
  let A : R3 →L[ℝ] R3 := -((ContinuousLinearMap.inverse (F y)).comp
    (fderiv ℝ F y X + (Γ y X).comp (F y)))
  have hA (w : R3) : A w = conformalReferenceParallelAngularVelocity g L q y X w := by
    simp only [A,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,conformalReferenceParallelAngularVelocity,
      framedParallelAngularVelocity,F,Γ]
  calc
    conformalReferenceParallelAngularVelocity g L q y X z = A z := (hA z).symm
    _ = A (∑ b : Fin 3, z b • NormalCoordinatesFrame.coordinateVector b) :=
      congrArg A (gramAngular_sum_coordinateVector z).symm
    _ = ∑ b : Fin 3, z b • A (NormalCoordinatesFrame.coordinateVector b) := by
      simp only [map_sum,map_smul]
    _ = ∑ b : Fin 3, z b • conformalReferenceParallelAngularVelocity g L q y X
        (NormalCoordinatesFrame.coordinateVector b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hA]

theorem conformalReferenceParallelAngularVelocity_component
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (y X z : R3) (a : Fin 3) :
    inner ℝ (conformalReferenceParallelAngularVelocity g L q y X z)
      (NormalCoordinatesFrame.coordinateVector a) =
      -∑ b : Fin 3, conformalReferenceFrameConnectionCoefficient g L q y X a b * z b := by
  calc
    inner ℝ (conformalReferenceParallelAngularVelocity g L q y X z)
        (NormalCoordinatesFrame.coordinateVector a) =
        ∑ b : Fin 3, z b * inner ℝ
          (conformalReferenceParallelAngularVelocity g L q y X
            (NormalCoordinatesFrame.coordinateVector b))
          (NormalCoordinatesFrame.coordinateVector a) := by
      rw [conformalReferenceParallelAngularVelocity_sum_coordinates]
      simp only [sum_inner,real_inner_smul_left]
    _ = ∑ b : Fin 3, -(conformalReferenceFrameConnectionCoefficient g L q y X a b * z b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [conformalReferenceParallelAngularVelocity_frame_component g hg L q y X a b]
      ring
    _ = -∑ b : Fin 3, conformalReferenceFrameConnectionCoefficient g L q y X a b * z b := by
      rw [Finset.sum_neg_distrib]

theorem conformalReferenceParallelAngularVelocity_inner_self_eq_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (y X z : R3) :
    inner ℝ (conformalReferenceParallelAngularVelocity g L q y X z) z = 0 := by
  let K : Fin 3 → Fin 3 → ℝ := conformalReferenceFrameConnectionCoefficient g L q y X
  let S : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, z a * z b * K a b
  have hExpansion : inner ℝ (conformalReferenceParallelAngularVelocity g L q y X z) z = -S := by
    calc
      inner ℝ (conformalReferenceParallelAngularVelocity g L q y X z) z =
          inner ℝ (conformalReferenceParallelAngularVelocity g L q y X z)
            (∑ a : Fin 3, z a • NormalCoordinatesFrame.coordinateVector a) := by
        rw [gramAngular_sum_coordinateVector]
      _ = ∑ a : Fin 3, z a * inner ℝ
          (conformalReferenceParallelAngularVelocity g L q y X z)
          (NormalCoordinatesFrame.coordinateVector a) := by
        simp only [inner_sum,real_inner_smul_right]
      _ = ∑ a : Fin 3, z a * (-∑ b : Fin 3, K a b * z b) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [conformalReferenceParallelAngularVelocity_component g hg L q y X z a]
      _ = -S := by
        dsimp only [S]
        simp only [mul_neg,Finset.sum_neg_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
  have hNeg : S = -S := by
    dsimp only [S]
    calc
      (∑ a : Fin 3, ∑ b : Fin 3, z a * z b * K a b) =
          ∑ a : Fin 3, ∑ b : Fin 3, z a * z b * (-K b a) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        change z a * z b * conformalReferenceFrameConnectionCoefficient g L q y X a b =
          z a * z b * (-conformalReferenceFrameConnectionCoefficient g L q y X b a)
        rw [conformalReferenceFrameConnectionCoefficient_skew g hg L q y X a b]
      _ = -(∑ a : Fin 3, ∑ b : Fin 3, z b * z a * K b a) := by
        simp only [mul_neg,Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = -(∑ a : Fin 3, ∑ b : Fin 3, z a * z b * K a b) := by
        rw [Finset.sum_comm]
  linarith only [hExpansion,hNeg]

theorem conformalReferenceParallelAngularVelocity_tangent_sphere
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (y X : R3)
    (z : Metric.sphere (0 : R3) 1) :
    conformalReferenceParallelAngularVelocity g L q y X (z : R3) ∈
      (mvfderiv (𝓡 2) ((↑) : Metric.sphere (0 : R3) 1 → R3) z).range := by
  rw [range_mvfderiv_subtypeVal (n := 2) z]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    (conformalReferenceParallelAngularVelocity_inner_self_eq_zero g hg L q y X (z : R3))

end OAI.AnisotropicCalderon.ConnectionError
