import Calderon.MetricOperator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator

def conformalReferenceCoordinateDepth (x : R3) : ℝ := x 2+x 0^2+x 1^2

def conformalReferenceMatrix (g : MatrixField) (L lam : ℝ) : MatrixField :=
  fun x => Real.exp (-2*L*conformalReferenceCoordinateDepth x) • g (lam • x)

def conformalReferenceOperatorJoint (g : MatrixField) (L : ℝ) (p : ℝ × R3) : R3 →L[ℝ] R3 :=
  metricOperatorField (conformalReferenceMatrix g L p.1) p.2

theorem contDiff_conformalReferenceCoordinateDepth : ContDiff ℝ ∞ conformalReferenceCoordinateDepth :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.add
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.pow 2)).add
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.pow 2)

theorem conformalReferenceOperatorJoint_eq (g : MatrixField) (L : ℝ) (p : ℝ × R3) :
    conformalReferenceOperatorJoint g L p =
      Real.exp (-2*L*conformalReferenceCoordinateDepth p.2) • metricOperatorField g (p.1 • p.2) :=
  matrixOperatorMap.map_smul _ _

theorem contDiff_conformalReferenceOperatorJoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (conformalReferenceOperatorJoint g L) := by
  have hDil : ContDiff ℝ ∞ (fun p : ℝ × R3 => p.1 • p.2) := contDiff_fst.smul contDiff_snd
  have hM := (contDiff_metricOperatorField g hg).comp hDil
  have ha : ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      Real.exp (-2*L*conformalReferenceCoordinateDepth p.2)) :=
    (contDiff_const.mul (contDiff_conformalReferenceCoordinateDepth.comp contDiff_snd)).exp
  have he : conformalReferenceOperatorJoint g L = fun p =>
      Real.exp (-2*L*conformalReferenceCoordinateDepth p.2) • metricOperatorField g (p.1 • p.2) :=
    funext (conformalReferenceOperatorJoint_eq g L)
  rw [he]
  exact ha.smul hM

theorem conformalReferenceOperatorJoint_symmetric (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (p : ℝ × R3) (u v : R3) :
    inner ℝ (conformalReferenceOperatorJoint g L p u) v =
      inner ℝ (conformalReferenceOperatorJoint g L p v) u := by
  rw [conformalReferenceOperatorJoint_eq]
  simp only [smul_apply,real_inner_smul_left,metricOperatorField_symmetric g hg]

theorem conformalReferenceOperatorJoint_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (p : ℝ × R3) (v : R3) (hv : v ≠ 0) :
    0 < inner ℝ (conformalReferenceOperatorJoint g L p v) v := by
  rw [conformalReferenceOperatorJoint_eq]
  simp only [smul_apply,real_inner_smul_left]
  have hvf : (v : Fin 3 → ℝ) ≠ 0 := by
    intro hz
    apply hv
    ext i
    exact congrFun hz i
  have hp := (hg.posDef (p.1 • p.2)).dotProduct_mulVec_pos hvf
  have hgpos : 0 < inner ℝ (metricOperatorField g (p.1 • p.2) v) v := by
    simpa [metricOperatorField_apply,EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.toEuclideanLin,Matrix.toLpLin_apply,dotProduct_comm] using hp
  exact mul_pos (Real.exp_pos _) hgpos

private instance instCompleteReferenceR3 : CompleteSpace R3 := FiniteDimensional.complete ℝ R3
private instance instCompleteReferenceOperator : CompleteSpace (R3 →L[ℝ] R3) := ContinuousLinearMap.instCompleteSpace

section GenericInverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_actual_operatorRingInverse (M : E → R3 →L[ℝ] R3)
    (hM : ContDiff ℝ ∞ M) (hunit : ∀ p, IsUnit (M p)) :
    ContDiff ℝ ∞ (fun p => Ring.inverse (M p)) := by
  letI : HasSummableGeomSeries (R3 →L[ℝ] R3) := inferInstance
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨u,hu⟩ := hunit p
  have hi : ContDiffAt ℝ ∞ Ring.inverse (M p) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hi.comp p hM.contDiffAt

end GenericInverse

theorem contDiff_conformalReferenceInverseJoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × R3 => Ring.inverse (conformalReferenceOperatorJoint g L p)) :=
  contDiff_actual_operatorRingInverse _ (contDiff_conformalReferenceOperatorJoint g hg L)
    (fun p => isUnit_of_strictly_positive _ (conformalReferenceOperatorJoint_pos g hg L p))

theorem conformalReference_slice_data (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) :
    ContDiff ℝ ∞ (metricOperatorField (conformalReferenceMatrix g L lam)) ∧
    ContDiff ℝ ∞ (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L lam))) ∧
    (∀ y u v, inner ℝ (metricOperatorField (conformalReferenceMatrix g L lam) y u) v =
      inner ℝ (metricOperatorField (conformalReferenceMatrix g L lam) y v) u) ∧
    (∀ y v, v ≠ 0 → 0 < inner ℝ (metricOperatorField (conformalReferenceMatrix g L lam) y v) v) ∧
    ∀ y v, metricOperatorField (conformalReferenceMatrix g L lam) y
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L lam)) y v) = v := by
  have hs : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hM : ContDiff ℝ ∞ (metricOperatorField (conformalReferenceMatrix g L lam)) := by
    simpa only [Function.comp_def,conformalReferenceOperatorJoint] using
      (contDiff_conformalReferenceOperatorJoint g hg L).comp hs
  have hunit : ∀ y, IsUnit (metricOperatorField (conformalReferenceMatrix g L lam) y) :=
    fun y => isUnit_of_strictly_positive _ (conformalReferenceOperatorJoint_pos g hg L (lam,y))
  have hQ := contDiff_inverseMetricField _ hM hunit
  refine ⟨hM,hQ,
    fun y => conformalReferenceOperatorJoint_symmetric g hg L (lam,y),
    fun y => conformalReferenceOperatorJoint_pos g hg L (lam,y),
    ?_⟩
  exact metric_apply_inverseMetricField _ hunit
end OAI.AnisotropicCalderon.ConnectionError
