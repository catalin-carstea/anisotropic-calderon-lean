import Calderon.ActualAdjointMovingBoundaryFamilyFoundation
import Calderon.SignedTaylorFixedLinearTransport
import Calderon.SphereSobolevDualOrthogonalPullback

/-! Signed Taylor remainder of the native lower transpose, for the same genuine pivot
transpose. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
open ConnectionError

local instance : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

attribute [local irreducible] sphereLowerDistributionalTranspose sphereLowerDistributionalTransposeL
  secondTaylorRemainder

lemma sphereLowerDistributionalTranspose_involutive
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
    sphereLowerDistributionalTranspose (sphereLowerDistributionalTranspose A) = A := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  have hT := sphereSobolevDualPairing_lower_distributionalTranspose
    (sphereLowerDistributionalTranspose A) z u
  have hA := sphereSobolevDualPairing_lower_distributionalTranspose A u z
  exact hT.symm.trans hA.symm

lemma sphereLowerDistributionalTranspose_secondTaylorRemainder
    (F : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))))
    (r : ℝ) (hF : ∀ a ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (a*r)) :
    sphereLowerDistributionalTranspose (secondTaylorRemainder F r) =
      secondTaylorRemainder (fun t => sphereLowerDistributionalTranspose (F t)) r := by
  letI : NormedAddCommGroup
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  let t : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    { toFun := sphereLowerDistributionalTranspose
      map_add' := fun A B => by
        have h := sphereLowerDistributionalTransposeL.map_add A B
        simpa only [sphereLowerDistributionalTransposeL_apply] using h
      map_smul' := fun c A => by
        have h := sphereLowerDistributionalTransposeL.map_smul c A
        simpa only [sphereLowerDistributionalTransposeL_apply,RingHom.id_apply] using h }
  have hBound : ∀ A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)),
      ‖t A‖ ≤ (1 : ℝ) * ‖A‖ := by
    intro A
    have hAdj : t A = ContinuousLinearMap.adjoint A := by
      change sphereLowerDistributionalTranspose A = ContinuousLinearMap.adjoint A
      unfold sphereLowerDistributionalTranspose sphereHalfDualCarrierEquiv
      apply ContinuousLinearMap.ext
      intro u
      rfl
    have hNorm : ‖t A‖ ≤ ‖A‖ :=
      (congrArg (fun B : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => ‖B‖) hAdj).le.trans
          (ContinuousLinearMap.adjoint.norm_map A).le
    simpa only [one_mul] using hNorm
  let L : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    LinearMap.mkContinuous
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      t (1 : ℝ) hBound
  have hApply (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
      L A = sphereLowerDistributionalTranspose A := rfl
  have hMap := secondTaylorRemainder_fixed_linear_map F L r hF
  have hCurve : (fun t => L (F t)) =
      (fun t => sphereLowerDistributionalTranspose (F t)) := by
    funext t
    exact hApply (F t)
  exact (hApply (secondTaylorRemainder F r)).symm.trans
    (hMap.trans (congrArg (fun G : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ))) => secondTaylorRemainder G r) hCurve))

lemma sphereLowerDistributionalTranspose_sub_self_skew
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
    sphereLowerDistributionalTranspose (sphereLowerDistributionalTranspose A-A) =
      -(sphereLowerDistributionalTranspose A-A) := by
  have hMap := sphereLowerDistributionalTransposeL.map_sub (sphereLowerDistributionalTranspose A) A
  have hSub : sphereLowerDistributionalTranspose (sphereLowerDistributionalTranspose A-A) =
      sphereLowerDistributionalTranspose (sphereLowerDistributionalTranspose A)-
        sphereLowerDistributionalTranspose A :=
    (sphereLowerDistributionalTransposeL_apply _).symm.trans
      (hMap.trans (congrArg₂ (fun U V : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => U-V)
        (sphereLowerDistributionalTransposeL_apply (sphereLowerDistributionalTranspose A))
        (sphereLowerDistributionalTransposeL_apply A)))
  exact hSub.trans ((congrArg (fun U : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => U-sphereLowerDistributionalTranspose A)
      (sphereLowerDistributionalTranspose_involutive A)).trans (by abel))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_involutive
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_secondTaylorRemainder
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_sub_self_skew
