import Calderon.MetricHessianTestEquiv
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
open MetricVolume

/-- Evaluate a continuous bilinear form on the standard Euclidean coordinate vectors. -/
def bilinearCoordinateMap : (R3 →L[ℝ] R3 →L[ℝ] ℝ) →L[ℝ] Mat :=
  ContinuousLinearMap.pi fun i : Fin 3 =>
    ContinuousLinearMap.pi fun j : Fin 3 =>
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j 1)).comp
        (ContinuousLinearMap.apply ℝ (R3 →L[ℝ] ℝ) (EuclideanSpace.single i 1))

@[simp]
theorem bilinearCoordinateMap_apply (A : R3 →L[ℝ] R3 →L[ℝ] ℝ) (i j : Fin 3) :
    bilinearCoordinateMap A i j = A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rfl

theorem norm_bilinearCoordinateMap_apply_le (A : R3 →L[ℝ] R3 →L[ℝ] ℝ) :
    ‖bilinearCoordinateMap A‖ ≤ ‖A‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg A)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg A)).2 fun j => ?_
  rw [bilinearCoordinateMap_apply]
  calc
    ‖A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤
        ‖A (EuclideanSpace.single i 1)‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
      (A (EuclideanSpace.single i 1)).le_opNorm _
    _ ≤ (‖A‖ * ‖EuclideanSpace.single i (1 : ℝ)‖) *
        ‖EuclideanSpace.single j (1 : ℝ)‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ = ‖A‖ := by simp

/-- Continuous linear postcomposition by a contraction does not increase any spatial jet norm. -/
theorem norm_iteratedFDeriv_comp_left_le_of_contracting
    (E F G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (hL : ∀ z : F, ‖L z‖ ≤ ‖z‖)
    (g : E → F) (x : E) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (L ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ n g x‖ := by
  have hNorm : ‖L‖ ≤ 1 :=
    L.opNorm_le_bound zero_le_one (fun z => by simpa only [one_mul] using hL z)
  calc
    ‖iteratedFDeriv ℝ n (L ∘ g) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n g x‖ :=
      L.norm_iteratedFDeriv_comp_left hg (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ n g x‖ :=
      mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n g x‖ := one_mul _

/-- Every spatial derivative of the coordinate Hessian is bounded by the corresponding
higher scalar derivative, with constant one for the inherited elementwise matrix norm. -/
theorem norm_iteratedFDeriv_coordinateHessian_le
    (f : R3 → ℝ) (x : R3) (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n
      (fun y : R3 => (fun i j : Fin 3 =>
        fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : Mat)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 2) f x‖ := by
  have hDf := hf.fderiv_right (m := ∞) (by simp)
  have hB := hDf.fderiv_right (m := ∞) (by simp)
  have hBound := @norm_iteratedFDeriv_comp_left_le_of_contracting
    R3 (R3 →L[ℝ] R3 →L[ℝ] ℝ) Mat _ _
    (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) _ _
    bilinearCoordinateMap norm_bilinearCoordinateMap_apply_le
    (fderiv ℝ (fderiv ℝ f)) x hB n
  have hNorm := @norm_iteratedFDeriv_fderiv ℝ _ R3 _ _ (R3 →L[ℝ] ℝ)
    (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ))
    (fderiv ℝ f) x n
  have hNorm' := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := n + 1)
  rw [hNorm, hNorm'] at hBound
  exact hBound

/-- Open-domain version of the constant-one spatial Hessian jet estimate. -/
theorem norm_iteratedFDeriv_coordinateHessian_le_of_isOpen
    (f : R3 → ℝ) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n
      (fun y : R3 => (fun i j : Fin 3 =>
        fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : Mat)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 2) f x‖ := by
  exact norm_iteratedFDeriv_coordinateHessian_le f x (hf.contDiffAt (hU.mem_nhds hx)) n

/-- A scalar derivative bound of order `n + 2` controls the genuine nth spatial
matrix-Hessian derivative on the same open domain. -/
theorem norm_iteratedFDeriv_coordinateHessian_le_of_bound
    (f : R3 → ℝ) (U : Set R3) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U) (n : ℕ) (C : ℝ)
    (hC : ‖iteratedFDeriv ℝ (n + 2) f x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n
      (fun y : R3 => (fun i j : Fin 3 =>
        fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : Mat)) x‖ ≤ C := by
  exact (norm_iteratedFDeriv_coordinateHessian_le_of_isOpen f U hU hf x hx n).trans hC

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
