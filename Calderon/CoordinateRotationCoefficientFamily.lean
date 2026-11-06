import Calderon.NativeOrthogonalCoefficientEnergyCovariance
import Calderon.SmoothSphereRotation
import Calderon.CoordinateRotationSmoothComposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator MetricVolume SmoothSphereRotation

/-! True angular coefficient family, not a reparameterization of the original coefficient family. -/

def coordinateRotationMatrix (i j : Fin 3) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  operatorMatrixMap (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap

lemma coordinateRotationMatrix_entry (i j k l : Fin 3) (θ : ℝ) :
    coordinateRotationMatrix i j θ k l = (coordinateRotation i j θ (coordinateVector l)) k := by
  have h := matrixOperator_basis_inner (coordinateRotationMatrix i j θ) k l
  change inner ℝ ((operatorMatrixMap _).toEuclideanLin (coordinateVector l)) (coordinateVector k) = _ at h
  rw [operatorMatrixMap_apply] at h
  change inner ℝ (coordinateRotation i j θ (coordinateVector l)) (coordinateVector k) =
    coordinateRotationMatrix i j θ k l at h
  simpa only [coordinateVector,EuclideanSpace.inner_single_right,one_mul,conj_trivial] using h.symm

lemma contDiff_coordinateRotationMatrix (i j : Fin 3) :
    ContDiff ℝ ∞ (coordinateRotationMatrix i j) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  have hr : ContDiff ℝ ∞ (fun θ : ℝ => coordinateRotation i j θ (coordinateVector l)) := by
    apply contDiff_coordinateRotation_of_smooth
    · exact contDiff_id
    · exact contDiff_const
  have he : (fun θ : ℝ => coordinateRotationMatrix i j θ k l) =
      fun θ : ℝ => (coordinateRotation i j θ (coordinateVector l)) k :=
    funext (coordinateRotationMatrix_entry i j k l)
  rw [he]
  apply (EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff.comp
  exact hr

lemma coordinateRotationMatrix_zero (i j : Fin 3) : coordinateRotationMatrix i j 0 = 1 := by
  ext k l
  rw [coordinateRotationMatrix_entry,coordinateRotation_zero]
  simp [coordinateVector,PiLp.single_apply,Matrix.one_apply,eq_comm]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def coordinateRotationPrincipalFamily (i j : Fin 3)
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) : (ℝ × P) × R3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun q => (coordinateRotationMatrix i j q.1.1)ᵀ *
    a (q.1.2,coordinateRotation i j q.1.1 q.2) * coordinateRotationMatrix i j q.1.1

def coordinateRotationDriftFamily (i j : Fin 3) (b : P × R3 → R3) : (ℝ × P) × R3 → R3 :=
  fun q => coordinateRotation i j (-q.1.1) (b (q.1.2,coordinateRotation i j q.1.1 q.2))

lemma coordinateRotationPrincipalFamily_eq_orthogonal (i j : Fin 3)
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) (p : P) (x : R3) :
    coordinateRotationPrincipalFamily i j a ((θ,p),x) =
      orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ) (fun z => a (p,z)) x :=
  (orthogonalPrincipalCoefficient_eq_matrix_conjugation
    (coordinateRotationIsometry i j θ) (fun z => a (p,z)) x).symm

lemma coordinateRotationDriftFamily_eq_orthogonal (i j : Fin 3)
    (b : P × R3 → R3) (θ : ℝ) (p : P) (x : R3) :
    coordinateRotationDriftFamily i j b ((θ,p),x) =
      orthogonalDriftCoefficient (coordinateRotationIsometry i j θ) (fun z => b (p,z)) x := rfl

lemma contDiff_coordinateRotationPrincipalFamily (i j : Fin 3)
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (coordinateRotationPrincipalFamily i j a) := by
  unfold coordinateRotationPrincipalFamily
  apply contDiff_matrix_conjugation_fields
  · apply (contDiff_coordinateRotationMatrix i j).comp
    exact contDiff_fst.fst
  · apply ha.comp
    exact contDiff_coordinateRotationSourceMap i j

lemma contDiff_coordinateRotationDriftFamily (i j : Fin 3)
    (b : P × R3 → R3) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (coordinateRotationDriftFamily i j b) := by
  unfold coordinateRotationDriftFamily
  apply contDiff_coordinateRotation_of_smooth
  · exact contDiff_fst.fst.neg
  · apply hb.comp
    exact contDiff_coordinateRotationSourceMap i j

lemma coordinateRotation_outside_closedBall (i j : Fin 3) (θ : ℝ) (x : R3) (R : ℝ)
    (hx : x ∉ Metric.closedBall (0 : R3) R) :
    coordinateRotation i j θ x ∉ Metric.closedBall (0 : R3) R := by
  simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using hx

lemma coordinateRotationPrincipalFamily_zero_outside (i j : Fin 3)
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ)
    (hz : ∀ p x, x ∉ Metric.closedBall (0 : R3) R → a (p,x) = 0)
    (t : ℝ × P) (x : R3) (hx : x ∉ Metric.closedBall (0 : R3) R) :
    coordinateRotationPrincipalFamily i j a (t,x) = 0 := by
  unfold coordinateRotationPrincipalFamily
  rw [hz t.2 (coordinateRotation i j t.1 x) (coordinateRotation_outside_closedBall i j t.1 x R hx)]
  simp only [mul_zero,zero_mul]

lemma coordinateRotationDriftFamily_zero_outside (i j : Fin 3) (b : P × R3 → R3) (R : ℝ)
    (hz : ∀ p x, x ∉ Metric.closedBall (0 : R3) R → b (p,x) = 0)
    (t : ℝ × P) (x : R3) (hx : x ∉ Metric.closedBall (0 : R3) R) :
    coordinateRotationDriftFamily i j b (t,x) = 0 := by
  unfold coordinateRotationDriftFamily
  rw [hz t.2 (coordinateRotation i j t.1 x) (coordinateRotation_outside_closedBall i j t.1 x R hx)]
  exact (coordinateRotationIsometry i j (-t.1)).map_zero

lemma coordinateRotationPrincipalFamily_zero_angle (i j : Fin 3)
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : P) (x : R3) :
    coordinateRotationPrincipalFamily i j a ((0,p),x) = a (p,x) := by
  simp only [coordinateRotationPrincipalFamily,coordinateRotationMatrix_zero,
    coordinateRotation_zero,Matrix.transpose_one,one_mul,mul_one]

lemma coordinateRotationDriftFamily_zero_angle (i j : Fin 3) (b : P × R3 → R3) (p : P) (x : R3) :
    coordinateRotationDriftFamily i j b ((0,p),x) = b (p,x) := by
  simp only [coordinateRotationDriftFamily,neg_zero,coordinateRotation_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationMatrix
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationMatrix_entry
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_coordinateRotationMatrix
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationMatrix_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationPrincipalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationDriftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationPrincipalFamily_eq_orthogonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationDriftFamily_eq_orthogonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_coordinateRotationPrincipalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_coordinateRotationDriftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotation_outside_closedBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationPrincipalFamily_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationDriftFamily_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationPrincipalFamily_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateRotationDriftFamily_zero_angle
