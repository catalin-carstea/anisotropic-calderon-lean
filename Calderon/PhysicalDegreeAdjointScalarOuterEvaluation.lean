import Calderon.PhysicalDegreeCasimirScalarFunctionalsCore
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic
/-! ORIGINAL literal two summands evaluated; no zero-equivalence/inner unfolding or
inherited-dictionary normalization is used. -/
lemma degreeAdjointScalarL_apply_outer_sub
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ij : Fin 3 × Fin 3) (f g : SphereSobolev 1) (x : PhysicalDegreeCasimirData) :
    degreeAdjointScalarL hO hD ij f g x =
      degreePrimalPhysicalScalarL hO hD ij f
        ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) g)) x -
      ((innerSL ℝ ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) f))).comp
          ((sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
            ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) g).comp (degreeAdjointProjectionL ij)))) x := by
  run_tac do let out ← IO.getStdout; out.putStrLn "OUTER_SUB_PROOF_ENTER"; out.flush
  let P : PhysicalDegreeCasimirData →L[ℝ] ℝ :=
    degreePrimalPhysicalScalarL hO hD ij f
      ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) g))
  let Q : PhysicalDegreeCasimirData →L[ℝ] ℝ :=
    (innerSL ℝ ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) f))).comp
        ((sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) g).comp (degreeAdjointProjectionL ij)))
  run_tac do let out ← IO.getStdout; out.putStrLn "OUTER_SUB_SUMMANDS_TYPED"; out.flush
  have hMap : degreeAdjointScalarL hO hD ij f g = P-Q := by rfl
  run_tac do let out ← IO.getStdout; out.putStrLn "OUTER_SUB_MAP_IDENTITY"; out.flush
  have hValue : (P-Q) x = P x-Q x := sub_apply P Q x
  exact (congrArg (fun A : PhysicalDegreeCasimirData →L[ℝ] ℝ => A x) hMap).trans hValue
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeAdjointScalarL_apply_outer_sub
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
