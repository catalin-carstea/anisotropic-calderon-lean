import Calderon.SphereSobolevDualRiesz
import Calderon.SphereSobolevInclusion
import Calderon.DenseRealLinearExtension
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped InnerProductSpace ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
/-! Actual weighted decoded input/test
partial sums and physical half-dual Riesz; complete unrestricted outputs. -/

lemma norm_negativeHalf_le_of_finite_half_dual_tests
    (f : SphereSobolev (-(1/2:ℝ))) (B : ℝ) (hB : 0 ≤ B)
    (hFinite : ∀ v ∈ sphereSobolevFiniteSupport (1/2:ℝ),
      |sphereSobolevDualPairing (1/2:ℝ) v f| ≤ B*‖v‖) : ‖f‖ ≤ B := by
  let ell : StrongDual ℝ (SphereSobolev (1/2:ℝ)) := innerSLFlip ℝ f
  have hEll (v : SphereSobolev (1/2:ℝ)) : ell v = sphereSobolevDualPairing (1/2:ℝ) v f := rfl
  have hAll (v : SphereSobolev (1/2:ℝ)) : |ell v| ≤ B*‖v‖ := by
    have hClosed : IsClosed {x : SphereSobolev (1/2:ℝ) | |ell x| ≤ B*‖x‖} :=
      isClosed_le ell.continuous.abs (continuous_const.mul continuous_norm)
    have hc := closure_minimal (s := sphereSobolevFiniteSupport (1/2:ℝ))
      (fun x hx => (congrArg abs (hEll x)).trans_le (hFinite x hx)) hClosed
    rw [closure_sphereSobolevFiniteSupport] at hc
    exact hc (mem_univ v)
  have hRiesz : sphereSobolevDualRieszL (1/2:ℝ) ell = f := by
    change (InnerProductSpace.toDual ℝ (SphereSobolev (1/2:ℝ))).symm ell = f
    apply (InnerProductSpace.toDual ℝ (SphereSobolev (1/2:ℝ))).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro v
    exact real_inner_comm f v
  have hNormEll : ‖ell‖ ≤ B := ell.opNorm_le_bound hB (fun v => by
    simpa only [Real.norm_eq_abs] using hAll v)
  calc
    ‖f‖ = ‖sphereSobolevDualRieszL (1/2:ℝ) ell‖ := congrArg norm hRiesz.symm
    _ = ‖ell‖ := norm_sphereSobolevDualRieszL_apply (1/2:ℝ) ell
    _ ≤ B := hNormEll

lemma norm_high_operator_le_of_finite_half_dual_pairs
    (T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hFinite : ∀ u ∈ sphereSobolevFiniteSupport (3/2:ℝ),
      ∀ v ∈ sphereSobolevFiniteSupport (1/2:ℝ),
        |sphereSobolevDualPairing (1/2:ℝ) v (T u)| ≤
          M*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖*‖v‖)
    (u : SphereSobolev (3/2:ℝ)) :
    ‖T u‖ ≤ M*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖ := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hCore (x : SphereSobolev (3/2:ℝ)) (hx : x ∈ sphereSobolevFiniteSupport (3/2:ℝ)) :
      ‖T x‖ ≤ M*‖I x‖ :=
    norm_negativeHalf_le_of_finite_half_dual_tests (T x) (M*‖I x‖) (by positivity) (hFinite x hx)
  have hClosed : IsClosed {x : SphereSobolev (3/2:ℝ) | ‖T x‖ ≤ M*‖I x‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul I.continuous.norm)
  have hc := closure_minimal (s := sphereSobolevFiniteSupport (3/2:ℝ)) hCore hClosed
  rw [closure_sphereSobolevFiniteSupport] at hc
  exact hc (mem_univ u)

lemma exists_half_extension_of_finite_half_dual_pairs
    (T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hFinite : ∀ u ∈ sphereSobolevFiniteSupport (3/2:ℝ),
      ∀ v ∈ sphereSobolevFiniteSupport (1/2:ℝ),
        |sphereSobolevDualPairing (1/2:ℝ) v (T u)| ≤
          M*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖*‖v‖) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ M ∧
      (∀ u : SphereSobolev (3/2:ℝ), S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) = T u) ∧
      (∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (T (sphereSobolevSingleL (3/2:ℝ) n z))) := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hd : DenseRange I := denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hb : ∀ u, ‖T u‖ ≤ M*‖I u‖ := norm_high_operator_le_of_finite_half_dual_pairs T M hM hFinite
  let S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := T.toLinearMap.extendOfNorm I.toLinearMap
  have hGraph (u : SphereSobolev (3/2:ℝ)) : S (I u) = T u :=
    DenseRealLinearExtension.extendOfNorm_apply_dense T.toLinearMap I.toLinearMap hd M hb u
  have hNorm (u : SphereSobolev (1/2:ℝ)) : ‖S u‖ ≤ M*‖u‖ :=
    DenseRealLinearExtension.norm_extendOfNorm_apply_dense T.toLinearMap I.toLinearMap hd M hb u
  refine ⟨S,S.opNorm_le_bound hM hNorm,hGraph,?_⟩
  intro m n z
  have hSingle := hGraph (sphereSobolevSingleL (3/2:ℝ) n z)
  rw [sphereSobolevInclusionL_single] at hSingle
  exact congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hSingle

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_negativeHalf_le_of_finite_half_dual_tests
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_high_operator_le_of_finite_half_dual_pairs
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.exists_half_extension_of_finite_half_dual_pairs
end OAI.AnisotropicCalderon.SphereHarmonic
