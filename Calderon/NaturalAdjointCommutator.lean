import Calderon.NaturalAngularAdjointIntegration

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NaturalAngularAdjoint
open PrincipalCommutator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma zero_scalar_second_commutator (i j : R3) (a : R3 → ℝ)
    (H : R3 → E →L[ℝ] E) (w : R3 → E)
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w) (x : R3) :
    H x (a x • directionalFDeriv i (directionalFDeriv j w) x) -
      a x • directionalFDeriv i (directionalFDeriv j (fun y => H y (w y))) x =
    -a x • directionalFDeriv i (directionalFDeriv j H) x (w x) -
      a x • directionalFDeriv j H x (directionalFDeriv i w x) -
      a x • directionalFDeriv i H x (directionalFDeriv j w x) := by
  rw [map_smul, directionalFDeriv_second_clm_apply i j H w hH hw]
  simp only [smul_add]
  module

lemma first_first_commutator (i k : R3) (G B : R3 → E →L[ℝ] E) (w : R3 → E)
    (hG : ContDiff ℝ ∞ G) (hB : ContDiff ℝ ∞ B) (hw : ContDiff ℝ ∞ w) (x : R3) :
    G x (directionalFDeriv k (fun y => B y (directionalFDeriv i w y)) x) -
      B x (directionalFDeriv i (fun y => G y (directionalFDeriv k w y)) x) =
    G x (directionalFDeriv k B x (directionalFDeriv i w x)) -
      B x (directionalFDeriv i G x (directionalFDeriv k w x)) +
      ((G x).comp (B x) - (B x).comp (G x))
        (directionalFDeriv k (directionalFDeriv i w) x) := by
  rw [directionalFDeriv_clm_apply k B _ hB (contDiff_directionalFDeriv i w hw),
    directionalFDeriv_clm_apply i G _ hG (contDiff_directionalFDeriv k w hw),
    directionalFDeriv_commute i k w hw x]
  simp only [map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  abel

lemma zero_first_commutator (i : R3) (H B : R3 → E →L[ℝ] E) (w : R3 → E)
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w) (x : R3) :
    H x (B x (directionalFDeriv i w x)) -
      B x (directionalFDeriv i (fun y => H y (w y)) x) =
    ((H x).comp (B x) - (B x).comp (H x)) (directionalFDeriv i w x) -
      B x (directionalFDeriv i H x (w x)) := by
  rw [directionalFDeriv_clm_apply i H w hH hw]
  simp only [map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  abel

lemma first_zero_commutator (k : R3) (G C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hC : ContDiff ℝ ∞ C) (hw : ContDiff ℝ ∞ w) (x : R3) :
    G x (directionalFDeriv k (fun y => C y (w y)) x) -
      C x (G x (directionalFDeriv k w x)) =
    G x (directionalFDeriv k C x (w x)) +
      ((G x).comp (C x) - (C x).comp (G x)) (directionalFDeriv k w x) := by
  rw [directionalFDeriv_clm_apply k C w hC hw]
  simp only [map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  abel

/-- Second-base part of the commutator of the computed zero defect and U.
 The computed H contains every μ/a/B*/C* derivative from the source formula. -/
theorem defect_zero_scalar_principal_commutator (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hw : ContDiff ℝ ∞ w) (hp : ∀ x, mu x ≠ 0) (i j : Fin 3) (x : R3) :
    defectZeroCoefficient v mu a B C x
      (a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) w) x) -
      a x i j • directionalFDeriv (v i) (directionalFDeriv (v j)
        (fun y => defectZeroCoefficient v mu a B C y (w y))) x =
    -a x i j • directionalFDeriv (v i)
      (directionalFDeriv (v j) (defectZeroCoefficient v mu a B C)) x (w x) -
    a x i j • directionalFDeriv (v j) (defectZeroCoefficient v mu a B C) x
      (directionalFDeriv (v i) w x) -
    a x i j • directionalFDeriv (v i) (defectZeroCoefficient v mu a B C) x
      (directionalFDeriv (v j) w x) := by
  exact zero_scalar_second_commutator (v i) (v j) (fun y => a y i j)
    (defectZeroCoefficient v mu a B C) w
    (contDiff_defectZeroCoefficient v mu a B C hm ha hB hC hp) hw x

/-- Actual angular coefficient commutators remain: no assumption G_k B_i = B_i G_k. -/
theorem defect_first_angular_first_commutator (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (w : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x, mu x ≠ 0) (i k : Fin 3) (x : R3) :
    defectFirstCoefficient v mu a B x k
      (directionalFDeriv (v k) (fun y => B i y (directionalFDeriv (v i) w y)) x) -
      B i x (directionalFDeriv (v i) (fun y => defectFirstCoefficient v mu a B y k
        (directionalFDeriv (v k) w y)) x) =
    defectFirstCoefficient v mu a B x k
      (directionalFDeriv (v k) (B i) x (directionalFDeriv (v i) w x)) -
      B i x (directionalFDeriv (v i) (fun y => defectFirstCoefficient v mu a B y k) x
        (directionalFDeriv (v k) w x)) +
    ((defectFirstCoefficient v mu a B x k).comp (B i x) -
      (B i x).comp (defectFirstCoefficient v mu a B x k))
        (directionalFDeriv (v k) (directionalFDeriv (v i) w) x) := by
  exact first_first_commutator (v i) (v k)
    (fun y => defectFirstCoefficient v mu a B y k) (B i) w
    (contDiff_defectFirstCoefficient v mu a B hm ha hB hp k) (hB i) hw x

/-- The computed zero defect paired with the actual first-base angular term. -/
theorem defect_zero_angular_first_commutator (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hw : ContDiff ℝ ∞ w) (hp : ∀ x, mu x ≠ 0) (i : Fin 3) (x : R3) :
    defectZeroCoefficient v mu a B C x (B i x (directionalFDeriv (v i) w x)) -
      B i x (directionalFDeriv (v i) (fun y => defectZeroCoefficient v mu a B C y (w y)) x) =
    ((defectZeroCoefficient v mu a B C x).comp (B i x) -
      (B i x).comp (defectZeroCoefficient v mu a B C x)) (directionalFDeriv (v i) w x) -
      B i x (directionalFDeriv (v i) (defectZeroCoefficient v mu a B C) x (w x)) := by
  exact zero_first_commutator (v i) (defectZeroCoefficient v mu a B C) (B i) w
    (contDiff_defectZeroCoefficient v mu a B C hm ha hB hC hp) hw x

/-- The computed first defect paired with the actual zero-base angular coefficient. -/
theorem defect_first_angular_zero_commutator (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hC : ContDiff ℝ ∞ C) (hw : ContDiff ℝ ∞ w) (k : Fin 3) (x : R3) :
    defectFirstCoefficient v mu a B x k
      (directionalFDeriv (v k) (fun y => C y (w y)) x) -
      C x (defectFirstCoefficient v mu a B x k (directionalFDeriv (v k) w x)) =
    defectFirstCoefficient v mu a B x k (directionalFDeriv (v k) C x (w x)) +
      ((defectFirstCoefficient v mu a B x k).comp (C x) -
        (C x).comp (defectFirstCoefficient v mu a B x k)) (directionalFDeriv (v k) w x) := by
  exact first_zero_commutator (v k) (fun y => defectFirstCoefficient v mu a B y k) C w hC hw x

/-- Final zero-base angular commutator is retained exactly. -/
lemma defect_zero_angular_zero_commutator (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (w : R3 → E) (x : R3) :
    defectZeroCoefficient v mu a B C x (C x (w x)) -
      C x (defectZeroCoefficient v mu a B C x (w x)) =
    ((defectZeroCoefficient v mu a B C x).comp (C x) -
      (C x).comp (defectZeroCoefficient v mu a B C x)) (w x) := rfl

end OAI.AnisotropicCalderon.NaturalAngularAdjoint
