import Calderon.ProfileMetricTensorJets
import Mathlib.LinearAlgebra.Multilinear.Basis

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.RadiusProfile

def bilinearCoordinateTensor (H : R3 →L[ℝ] R3 →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => R3) ℝ :=
  (((continuousMultilinearCurryFin1 ℝ R3 ℝ).symm.toContinuousLinearMap).comp H).uncurryLeft

lemma bilinearCoordinateTensor_apply (H : R3 →L[ℝ] R3 →L[ℝ] ℝ) (V : Fin 2 → R3) :
    bilinearCoordinateTensor H V = H (V 0) (V 1) := by
  simp [bilinearCoordinateTensor, ContinuousLinearMap.uncurryLeft_apply, Fin.tail]

def coordinateHessianBilinear (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) (x : R3) : R3 →L[ℝ] R3 →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ R3 R3 ℝ (fderiv ℝ f x)).comp (Γ (lam, x))

lemma coordinateHessianBilinear_apply (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) (x X Y : R3) :
    coordinateHessianBilinear Γ f lam x X Y =
      coordinateHessian f (fun V W => Γ (lam, x) V W) x X Y := by
  rfl

theorem covariantCoordinateTensor_two_eq_bilinearCoordinateTensor
    (Γ : CoordinateConnectionFamily) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (x : R3) :
    covariantCoordinateTensor Γ f lam 2 x =
      bilinearCoordinateTensor (coordinateHessianBilinear Γ f lam x) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin 2 => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
  intro I
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change covariantCoordinateTensor Γ f lam 2 x (fun j => jetBasisVector (I j)) =
    bilinearCoordinateTensor (coordinateHessianBilinear Γ f lam x) (fun j => jetBasisVector (I j))
  rw [covariantCoordinateTensor_basis, bilinearCoordinateTensor_apply, coordinateHessianBilinear_apply]
  have hI : I = Fin.cons (I 0) (Fin.cons (I 1) Fin.elim0) := by
    ext j
    fin_cases j <;> rfl
  conv_lhs => rw [hI]
  exact covariantCoordinateJet_two_eq_coordinateHessian Γ f hf lam x (I 0) (I 1)

theorem covariantCoordinateTensor_two_eq_coordinateHessian
    (Γ : CoordinateConnectionFamily) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (x X Y : R3) :
    covariantCoordinateTensor Γ f lam 2 x (Fin.cons X (Fin.cons Y Fin.elim0)) =
      coordinateHessian f (fun V W => Γ (lam, x) V W) x X Y := by
  rw [covariantCoordinateTensor_two_eq_bilinearCoordinateTensor Γ f hf,
    bilinearCoordinateTensor_apply, coordinateHessianBilinear_apply]
  rfl

def IsMetricOrthonormalFrame (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) : Prop :=
  ∀ i j, ⟪M (e i), e j⟫_ℝ = if i = j then 1 else 0

lemma IsMetricOrthonormalFrame_unit (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (i : Fin 3) : ⟪M (e i), e i⟫_ℝ = 1 := by
  simpa using he i i

end OAI.AnisotropicCalderon.RadiusProfile

namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile AngularPolynomial MetricOperator ConnectionError

theorem exists_dilated_referenceRadius_fixed_uniform_covariant_metric_frame_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ e : Fin 3 → R3,
        IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
        Real.sqrt (tensorFrameSquare n
          (covariantCoordinateTensor (referenceConnectionFamily g L)
            (fun y => Real.log (referenceRadius δ R p L y)) lam n x) e) ≤
          Cn * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  obtain ⟨Cn, hCn, h⟩ :=
    exists_dilated_referenceRadius_fixed_uniform_covariant_frame_norm_bound g hg L hL K hK n hn
  refine ⟨Cn, hCn, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx e he
  exact h lam hlam δ hδ hδ1 R hR p hp x hx e
    (fun i => (IsMetricOrthonormalFrame_unit _ _ he i).le)

theorem exists_dilated_referenceRadius_fixed_uniform_covariant_jets_one_to_eight_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ n : ℕ, 1 ≤ n → n ≤ 8 → ∀ e : Fin 3 → R3,
        IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
        Real.sqrt (tensorFrameSquare n
          (covariantCoordinateTensor (referenceConnectionFamily g L)
            (fun y => Real.log (referenceRadius δ R p L y)) lam n x) e) ≤
          C * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  choose J hJ using fun i : Fin 8 =>
    exists_dilated_referenceRadius_fixed_uniform_covariant_metric_frame_bound g hg L hL K hK
      (i.val + 1) (by omega)
  let S : ℝ := ∑ i : Fin 8, J i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hJ i).1.le)
  refine ⟨S + 1, by linarith, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx n hn hn8 e he
  let i : Fin 8 := ⟨n - 1, by omega⟩
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have h := (hJ i).2 lam hlam δ hδ hδ1 R hR p hp x hx
  rw [hi] at h
  have hbound := h e he
  have hsingle : J i ≤ S :=
    Finset.single_le_sum (s := Finset.univ) (a := i) (f := J)
      (fun j _ => (hJ j).1.le) (Finset.mem_univ i)
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith)
    (pow_nonneg (Real.sqrt_nonneg _) n))

end OAI.AnisotropicCalderon.ConformalDepth
