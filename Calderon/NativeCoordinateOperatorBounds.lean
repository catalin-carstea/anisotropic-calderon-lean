import Calderon.LocalCoordinateWordEqOnTransport
import Calderon.LocalLpFiniteDifferenceRemainder
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology ContDiff BigOperators
namespace OAI.AnisotropicCalderon
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds

lemma norm_clm_le_three_mul_of_coordinate_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : R3 →L[ℝ] V) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ i : Fin 3, ‖T (coordinateDirection i)‖ ≤ C) :
    ‖T‖ ≤ 3*C := by
  apply T.opNorm_le_bound (mul_nonneg (by norm_num) hC)
  intro v
  have hValue : T v = ∑ i : Fin 3, v i • T (coordinateDirection i) := by
    conv_lhs => rw [ActualReferenceDecomposition.vector_eq_sum_coordinateDirection v]
    simp only [map_sum, map_smul]
  calc
    ‖T v‖ = ‖∑ i : Fin 3, v i • T (coordinateDirection i)‖ := congrArg norm hValue
    _ ≤ ∑ i : Fin 3, ‖v i • T (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v i) (hBound i)
        (norm_nonneg _) (norm_nonneg _)
    _ = (3*C) * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma norm_fderiv_sub_le_nine_mul_of_coordinateWord_two_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : R3 → V) (O : Set R3) (hO : IsOpen O) (hConvex : Convex ℝ O)
    (hf : ContDiffOn ℝ ∞ f O) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ p ∈ O, ∀ i j : Fin 3,
      ‖coordinateFieldWordPartial [j,i] f p‖ ≤ M)
    (x y : R3) (hx : x ∈ O) (hy : y ∈ O) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ 9*M*‖y-x‖ := by
  have hWord (i : Fin 3) : ContDiffOn ℝ ∞ (coordinateFieldWordPartial [i] f) O :=
    ActualReferenceLocalCoordinateWordJets.contDiffOn_coordinateFieldWordPartial [i] f O hO hf
  have hDerivative (i : Fin 3) (p : R3) (hp : p ∈ O) :
      ‖fderiv ℝ (coordinateFieldWordPartial [i] f) p‖ ≤ 3*M := by
    apply norm_clm_le_three_mul_of_coordinate_bound _ M hM
    intro j
    simpa only [coordinateFieldWordPartial, PrincipalCommutator.directionalFDeriv] using
      hBound p hp i j
  have hCoordinate (i : Fin 3) :
      ‖coordinateFieldWordPartial [i] f y - coordinateFieldWordPartial [i] f x‖ ≤
        (3*M)*‖y-x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun p hp => ((hWord i).contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
      (hDerivative i) hConvex hx hy
  have hNorm : ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ 3*((3*M)*‖y-x‖) := by
    apply norm_clm_le_three_mul_of_coordinate_bound _ _
      (mul_nonneg (mul_nonneg (by norm_num) hM) (norm_nonneg _))
    intro i
    simpa only [ContinuousLinearMap.sub_apply, coordinateFieldWordPartial,
      PrincipalCommutator.directionalFDeriv] using hCoordinate i
  calc
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ 3*((3*M)*‖y-x‖) := hNorm
    _ = 9*M*‖y-x‖ := by ring

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.norm_clm_le_three_mul_of_coordinate_bound
#print axioms OAI.AnisotropicCalderon.norm_fderiv_sub_le_nine_mul_of_coordinateWord_two_bound
