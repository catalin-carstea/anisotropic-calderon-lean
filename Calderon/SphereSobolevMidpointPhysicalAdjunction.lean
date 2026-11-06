import Calderon.NativeHarmonicHalfCoarseDualPairing
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open NativeHarmonicHalfCoarseDualPairing

lemma sphereSobolevDualPairing_half_inclusion_one_zero
    (v : SphereSobolev 1) (y : SphereSobolev 0) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) y) =
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) v,y⟫_ℝ := by
  have hZero := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)
    (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) y
  have hTrans := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v)
    (sphereSobolevInclusionL_trans 1 (1/2:ℝ) 0 (by norm_num) (by norm_num))
  exact hZero.trans (congrArg (fun z : SphereSobolev 0 => ⟪z,y⟫_ℝ) hTrans)

lemma inner_midpoint_of_half_dual_pairing
    (A B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (M N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hM : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp M =
      A.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hN : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp N =
      B.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hPair : ∀ u v : SphereSobolev (1/2:ℝ),
      sphereSobolevDualPairing (1/2:ℝ) v (A u) = sphereSobolevDualPairing (1/2:ℝ) u (B v))
    (u v : SphereSobolev 1) :
    ⟪M u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N v⟫_ℝ := by
  let I := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hMu : J (M u)=A (I u) := congrArg
    (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) hM
  have hNv : J (N v)=B (I v) := congrArg
    (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T v) hN
  exact (real_inner_comm _ _).trans
    ((sphereSobolevDualPairing_half_inclusion_one_zero v (M u)).symm.trans
      ((congrArg (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (I v) y) hMu).trans
        ((hPair (I u) (I v)).trans
          ((congrArg (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (I u) y) hNv.symm).trans
            (sphereSobolevDualPairing_half_inclusion_one_zero u (N v))))))

lemma inner_probability_midpoint_of_half_dual_pairing
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (M N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hM : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp M =
      A.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hN : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp N =
      B.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hPair : ∀ u v : SphereSobolev (1/2:ℝ),
      sphereSobolevDualPairing (1/2:ℝ) v (A u) = sphereSobolevDualPairing (1/2:ℝ) u (B v))
    (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm (M u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm (N v)⟫_ℝ :=
  ((sphereSobolevZeroEquiv hO hD).symm.inner_map_map _ _).trans
    ((inner_midpoint_of_half_dual_pairing A B M N hM hN hPair u v).trans
      ((sphereSobolevZeroEquiv hO hD).symm.inner_map_map _ _).symm)

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_half_inclusion_one_zero
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_midpoint_of_half_dual_pairing
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_probability_midpoint_of_half_dual_pairing
