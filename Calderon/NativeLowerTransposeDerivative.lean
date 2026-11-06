import Calderon.NativeLowerTransposeSignedTaylor

/-! Derivative of the genuine lower transpose, with proof-local normed outer packaging only. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open ConnectionError

local instance : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

attribute [local irreducible] sphereLowerDistributionalTranspose sphereLowerDistributionalTransposeL

lemma sphereLowerDistributionalTranspose_hasDerivAt
    (F : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))))
    (F' : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (r : ℝ) (hF : HasDerivAt F F' r) :
    HasDerivAt (fun t => sphereLowerDistributionalTranspose (F t))
      (sphereLowerDistributionalTranspose F') r := by
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
  have hT := L.hasFDerivAt.comp_hasDerivAt r hF
  have hEq : (fun t => sphereLowerDistributionalTranspose (F t)) =ᶠ[𝓝 r]
      (fun t => L (F t)) :=
    Filter.Eventually.of_forall (fun t => (hApply (F t)).symm)
  exact (hT.congr_of_eventuallyEq hEq).congr_deriv (hApply F')

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_hasDerivAt
