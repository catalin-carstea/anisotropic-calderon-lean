import Calderon.SphereSobolevTraceReconstruction

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-H3-TRACE-EXPANSION-v001.md, Component B. Same bounded stored maps; exact shifted decoded graph. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection SpectralWeightedGraph

def sphereSobolevFiveHalfTraceReconstructionIdentityL :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (5/2 : ℝ) :=
  sphereSobolevTraceReconstructionIdentityL

def sphereSobolevFiveHalfTraceReconstructionRotationL (i j : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (5/2 : ℝ) :=
  sphereSobolevTraceReconstructionRotationL i j

lemma sphereSobolevFiveHalfTraceReconstruction_stored
    (u : SphereSobolev (3/2 : ℝ)) (v : Fin 3 → Fin 3 → SphereSobolev (3/2 : ℝ))
    (hGraph : ∀ i j k, v i j k = harmonicSphereRotation k i j (u k)) (k : ℕ) :
    (sphereSobolevFiveHalfTraceReconstructionIdentityL u +
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevFiveHalfTraceReconstructionRotationL i j (v i j)) k =
      (1+(k : ℝ)) • u k := by
  exact sphereSobolevTraceReconstruction_stored u v hGraph k

lemma besselWeight_fiveHalf_reconstruction (k : ℕ) :
    besselWeight (-(5/2 : ℝ)) k * (1+(k : ℝ)) = besselWeight (-(3/2 : ℝ)) k := by
  unfold besselWeight
  calc
    (1+(k : ℝ)) ^ (-(5/2 : ℝ)) * (1+(k : ℝ)) =
        (1+(k : ℝ)) ^ (-(5/2 : ℝ)) * (1+(k : ℝ)) ^ (1 : ℝ) :=
      congrArg (fun t : ℝ => (1+(k : ℝ)) ^ (-(5/2 : ℝ)) * t) (Real.rpow_one (1+(k : ℝ))).symm
    _ = (1+(k : ℝ)) ^ (-(5/2 : ℝ)+1) :=
      (Real.rpow_add (by positivity : 0 < 1+(k : ℝ)) (-(5/2 : ℝ)) 1).symm
    _ = (1+(k : ℝ)) ^ (-(3/2 : ℝ)) := by norm_num

lemma sphereSobolevCoefficientL_fiveHalfTraceReconstruction
    (u : SphereSobolev (3/2 : ℝ)) (v : Fin 3 → Fin 3 → SphereSobolev (3/2 : ℝ))
    (hGraph : ∀ i j k, v i j k = harmonicSphereRotation k i j (u k)) (k : ℕ) :
    sphereSobolevCoefficientL (5/2 : ℝ) k
      (sphereSobolevFiveHalfTraceReconstructionIdentityL u +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevFiveHalfTraceReconstructionRotationL i j (v i j)) =
      sphereSobolevCoefficientL (3/2 : ℝ) k u := by
  change besselWeight (-(5/2 : ℝ)) k •
      ((sphereSobolevFiveHalfTraceReconstructionIdentityL u +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevFiveHalfTraceReconstructionRotationL i j (v i j)) k) =
    besselWeight (-(3/2 : ℝ)) k • u k
  rw [sphereSobolevFiveHalfTraceReconstruction_stored u v hGraph k,smul_smul,
    besselWeight_fiveHalf_reconstruction]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevFiveHalfTraceReconstructionIdentityL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevFiveHalfTraceReconstructionRotationL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevFiveHalfTraceReconstruction_stored
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.besselWeight_fiveHalf_reconstruction
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_fiveHalfTraceReconstruction
