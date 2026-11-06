import Calderon.SignedTaylorFixedLinearTransport
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError

lemma secondTaylorRemainder_fixed_commutator
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : ℝ → X →L[ℝ] Y) (M : X →L[ℝ] X) (N : Y →L[ℝ] Y) (r : ℝ)
    (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (θ*r)) :
    secondTaylorRemainder (fun t => (F t).comp M-N.comp (F t)) r =
      (secondTaylorRemainder F r).comp M-N.comp (secondTaylorRemainder F r) := by
  let preLinear : (X →L[ℝ] Y) →ₗ[ℝ] (X →L[ℝ] Y) :=
    { toFun := fun T => T.comp M
      map_add' := fun T U => rfl
      map_smul' := fun c T => rfl }
  have hPreBound (T : X →L[ℝ] Y) : ‖preLinear T‖ ≤ ‖M‖*‖T‖ :=
    (T.opNorm_comp_le M).trans_eq (mul_comm _ _)
  let Pre : (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] Y) :=
    LinearMap.mkContinuous preLinear ‖M‖ hPreBound
  let postLinear : (X →L[ℝ] Y) →ₗ[ℝ] (X →L[ℝ] Y) :=
    { toFun := fun T => N.comp T
      map_add' := fun T U => by
        apply ContinuousLinearMap.ext
        intro x
        exact N.map_add (T x) (U x)
      map_smul' := fun c T => by
        apply ContinuousLinearMap.ext
        intro x
        exact N.map_smul c (T x) }
  let Post : (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] Y) :=
    LinearMap.mkContinuous postLinear ‖N‖ (fun T => N.opNorm_comp_le T)
  have hTransport := secondTaylorRemainder_fixed_linear_map F (Pre-Post) r hF
  have hCurve : (fun t => (Pre-Post) (F t)) =
      (fun t => (F t).comp M-N.comp (F t)) := rfl
  have hValue : (Pre-Post) (secondTaylorRemainder F r) =
      (secondTaylorRemainder F r).comp M-N.comp (secondTaylorRemainder F r) := rfl
  exact (congrArg (fun G => secondTaylorRemainder G r) hCurve).symm.trans
    (hTransport.symm.trans hValue)

lemma secondTaylorRemainder_const_smul_precomp
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ℝ → X →L[ℝ] Y) (I : Z →L[ℝ] X) (s r : ℝ)
    (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (θ*r)) :
    secondTaylorRemainder (fun t => s • (F t).comp I) r =
      s • (secondTaylorRemainder F r).comp I := by
  let preLinear : (X →L[ℝ] Y) →ₗ[ℝ] (Z →L[ℝ] Y) :=
    { toFun := fun T => s • T.comp I
      map_add' := fun T U => by
        apply ContinuousLinearMap.ext
        intro z
        exact smul_add s (T (I z)) (U (I z))
      map_smul' := fun c T => by
        apply ContinuousLinearMap.ext
        intro z
        exact smul_comm s c (T (I z)) }
  have hPreBound (T : X →L[ℝ] Y) : ‖preLinear T‖ ≤ (|s| *‖I‖)*‖T‖ := by
    calc
      _ ≤ ‖s‖*‖T.comp I‖ := ContinuousLinearMap.opNorm_smul_le s (T.comp I)
      _ ≤ ‖s‖*(‖T‖*‖I‖) :=
        mul_le_mul_of_nonneg_left (T.opNorm_comp_le I) (norm_nonneg s)
      _ = _ := by rw [Real.norm_eq_abs]; ring
  let Pre : (X →L[ℝ] Y) →L[ℝ] (Z →L[ℝ] Y) :=
    LinearMap.mkContinuous preLinear (|s| *‖I‖) hPreBound
  exact (secondTaylorRemainder_fixed_linear_map F Pre r hF).symm

end OAI.AnisotropicCalderon.ConnectionError
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_fixed_commutator
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_const_smul_precomp
