import Calderon.SphereSobolevTraceReconstruction

/-! Full upfront: full-physical-U-form-author-oct16-v001/
lower-rotation-reconstruction-author-v001/EXPANSION.md. Genuine distribution
witnesses and exact decoded native inclusion, without an output-regularity premise. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection SpectralWeightedGraph

def sphereSobolevLowerRotationReconstruction
    (z : SphereSobolev (-(1/2 : ℝ)))
    (v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ))) : SphereSobolev (1/2 : ℝ) :=
  sphereSobolevTraceReconstructionIdentityL z +
    ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)

lemma norm_sphereSobolevTraceReconstructionIdentityL_le :
    ‖sphereSobolevTraceReconstructionIdentityL‖ ≤ 1 := by
  unfold sphereSobolevTraceReconstructionIdentityL
  exact lp.norm_mapCLM_le _ _ _ _

lemma norm_sphereSobolevTraceReconstructionRotationL_le (i j : Fin 3) :
    ‖sphereSobolevTraceReconstructionRotationL i j‖ ≤ Real.sqrt 2 := by
  unfold sphereSobolevTraceReconstructionRotationL
  exact lp.norm_mapCLM_le _ _ _ _

lemma sphereSobolevRotationWitness_stored
    (z : SphereSobolev (-(1/2 : ℝ)))
    (v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)))
    (hGraph : ∀ i j : Fin 3,
      sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) (v i j) =
        sphereSobolevRotationL (-(1/2 : ℝ)) i j z) :
    ∀ i j k, v i j k = harmonicSphereRotation k i j (z k) := by
  intro i j k
  have hCoeff := congrArg (sphereSobolevCoefficientL (-(3/2 : ℝ)) k) (hGraph i j)
  have hRot : sphereSobolevCoefficientL (-(3/2 : ℝ)) k
      (sphereSobolevRotationL (-(1/2 : ℝ)) i j z) =
      harmonicSphereRotation k i j (sphereSobolevCoefficientL (-(1/2 : ℝ)) k z) := by
    have hIndex : (-(1/2 : ℝ)) - 1 = -(3/2 : ℝ) := by norm_num
    have hIndexMap (s t : ℝ) (hst : s = t) :
        (sphereSobolevCoefficientL s k :
          SphereSobolev (-(3/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k) =
          sphereSobolevCoefficientL t k := by
      cases hst
      rfl
    have hMaps := hIndexMap ((-(1/2 : ℝ)) - 1) (-(3/2 : ℝ)) hIndex
    have hEval := congrArg (fun F : SphereSobolev (-(3/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k =>
      F (sphereSobolevRotationL (-(1/2 : ℝ)) i j z)) hMaps
    exact hEval.symm.trans (sphereSobolevCoefficientL_rotation (-(1/2 : ℝ)) i j k z)
  have hDecoded : sphereSobolevCoefficientL (-(1/2 : ℝ)) k (v i j) =
      harmonicSphereRotation k i j (sphereSobolevCoefficientL (-(1/2 : ℝ)) k z) :=
    (sphereSobolevCoefficientL_inclusion (-(1/2 : ℝ)) (-(3/2 : ℝ))
      (by norm_num) (v i j) k).symm.trans (hCoeff.trans hRot)
  change besselWeight (-(-(1/2 : ℝ))) k • v i j k =
    harmonicSphereRotation k i j (besselWeight (-(-(1/2 : ℝ))) k • z k) at hDecoded
  rw [map_smul] at hDecoded
  have hCancel := congrArg (fun a : harmonicSphereSubspace k =>
    (besselWeight (-(-(1/2 : ℝ))) k)⁻¹ • a) hDecoded
  simpa only [smul_smul, inv_mul_cancel₀ (besselWeight_pos (-(-(1/2 : ℝ))) k).ne',
    one_smul] using hCancel

lemma besselWeight_half_lowerReconstruction (k : ℕ) :
    besselWeight (-(1/2 : ℝ)) k * (1 + (k : ℝ)) =
      besselWeight (-(-(1/2 : ℝ))) k := by
  unfold besselWeight
  calc
    (1 + (k : ℝ)) ^ (-(1/2 : ℝ)) * (1 + (k : ℝ)) =
        (1 + (k : ℝ)) ^ (-(1/2 : ℝ)) * (1 + (k : ℝ)) ^ (1 : ℝ) :=
      congrArg (fun t : ℝ => (1 + (k : ℝ)) ^ (-(1/2 : ℝ)) * t)
        (Real.rpow_one (1 + (k : ℝ))).symm
    _ = (1 + (k : ℝ)) ^ ((-(1/2 : ℝ)) + 1) :=
      (Real.rpow_add (by positivity : 0 < 1 + (k : ℝ)) (-(1/2 : ℝ)) 1).symm
    _ = (1 + (k : ℝ)) ^ (-(-(1/2 : ℝ))) := by norm_num

lemma sphereSobolevCoefficientL_lowerRotationReconstruction
    (z : SphereSobolev (-(1/2 : ℝ)))
    (v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)))
    (hGraph : ∀ i j : Fin 3,
      sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) (v i j) =
        sphereSobolevRotationL (-(1/2 : ℝ)) i j z) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (sphereSobolevLowerRotationReconstruction z v) =
      sphereSobolevCoefficientL (-(1/2 : ℝ)) k z := by
  have hStored := sphereSobolevRotationWitness_stored z v hGraph
  change besselWeight (-(1/2 : ℝ)) k •
      ((sphereSobolevTraceReconstructionIdentityL z +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)) k) =
    besselWeight (-(-(1/2 : ℝ))) k • z k
  rw [sphereSobolevTraceReconstruction_stored z v hStored k, smul_smul,
    besselWeight_half_lowerReconstruction]

lemma sphereSobolevInclusion_lowerRotationReconstruction
    (z : SphereSobolev (-(1/2 : ℝ)))
    (v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)))
    (hGraph : ∀ i j : Fin 3,
      sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) (v i j) =
        sphereSobolevRotationL (-(1/2 : ℝ)) i j z) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevLowerRotationReconstruction z v) = z := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  rw [sphereSobolevCoefficientL_inclusion]
  exact sphereSobolevCoefficientL_lowerRotationReconstruction z v hGraph k

lemma norm_sphereSobolevLowerRotationReconstruction_le
    (z : SphereSobolev (-(1/2 : ℝ)))
    (v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ))) :
    ‖sphereSobolevLowerRotationReconstruction z v‖ ≤
      ‖z‖ + Real.sqrt 2 * ∑ i : Fin 3, ∑ j : Fin 3, ‖v i j‖ := by
  have hId : ‖sphereSobolevTraceReconstructionIdentityL z‖ ≤ ‖z‖ := by
    simpa only [one_mul] using sphereSobolevTraceReconstructionIdentityL.le_of_opNorm_le
      norm_sphereSobolevTraceReconstructionIdentityL_le z
  have hSum : ‖∑ i : Fin 3, ∑ j : Fin 3,
      sphereSobolevTraceReconstructionRotationL i j (v i j)‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3, Real.sqrt 2 * ‖v i j‖ := by
    calc
      _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
          sphereSobolevTraceReconstructionRotationL i j (v i j)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖sphereSobolevTraceReconstructionRotationL i j (v i j)‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (sphereSobolevTraceReconstructionRotationL i j).le_of_opNorm_le
          (norm_sphereSobolevTraceReconstructionRotationL_le i j) (v i j)
  calc
    _ ≤ ‖sphereSobolevTraceReconstructionIdentityL z‖ +
        ‖∑ i : Fin 3, ∑ j : Fin 3,
          sphereSobolevTraceReconstructionRotationL i j (v i j)‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ∑ i : Fin 3, ∑ j : Fin 3, Real.sqrt 2 * ‖v i j‖ :=
      add_le_add hId hSum
    _ = _ := by simp_rw [Finset.mul_sum]

theorem exists_sphereSobolev_half_of_rotation_witnesses
    (z : SphereSobolev (-(1/2 : ℝ)))
    (v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)))
    (hGraph : ∀ i j : Fin 3,
      sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) (v i j) =
        sphereSobolevRotationL (-(1/2 : ℝ)) i j z) :
    ∃ zplus : SphereSobolev (1/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) zplus = z ∧
      ‖zplus‖ ≤ ‖z‖ + Real.sqrt 2 * ∑ i : Fin 3, ∑ j : Fin 3, ‖v i j‖ :=
  ⟨sphereSobolevLowerRotationReconstruction z v,
    sphereSobolevInclusion_lowerRotationReconstruction z v hGraph,
    norm_sphereSobolevLowerRotationReconstruction_le z v⟩

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevLowerRotationReconstruction
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevTraceReconstructionIdentityL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevTraceReconstructionRotationL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationWitness_stored
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.besselWeight_half_lowerReconstruction
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_lowerRotationReconstruction
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusion_lowerRotationReconstruction
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevLowerRotationReconstruction_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.exists_sphereSobolev_half_of_rotation_witnesses
