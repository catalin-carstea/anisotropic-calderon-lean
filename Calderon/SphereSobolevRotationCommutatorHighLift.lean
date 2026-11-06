import Calderon.SphereSobolevLowerRotationReconstruction

/-! Full upfront: full-physical-U-form-author-oct16-v001/
rotation-commutator-high-lift-author-v001/EXPANSION.md. Explicit finite CLM,
true lower distribution witnesses, no assumed high gain or output realization. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

def sphereSobolevRotationCommutatorHighLiftL
    (C : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (D : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  sphereSobolevTraceReconstructionIdentityL.comp
      (C.comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))) +
    ∑ i : Fin 3, ∑ j : Fin 3,
      (sphereSobolevTraceReconstructionRotationL i j).comp
        (C.comp (sphereSobolevRotationL (3/2 : ℝ) i j) +
          (D i j).comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)))

lemma sphereSobolevRotationCommutatorHighLiftL_apply
    (C : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (D : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevRotationCommutatorHighLiftL C D u =
      sphereSobolevLowerRotationReconstruction
        (C (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u))
        (fun i j => C (sphereSobolevRotationL (3/2 : ℝ) i j u) +
          D i j (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)) := by
  simp only [sphereSobolevRotationCommutatorHighLiftL,
    sphereSobolevLowerRotationReconstruction, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]

lemma norm_sphereSobolevRotationCommutatorHighLiftL_le
    (C : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (D : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
    ‖sphereSobolevRotationCommutatorHighLiftL C D‖ ≤
      19 * ‖C‖ + Real.sqrt 2 * ∑ i : Fin 3, ∑ j : Fin 3, ‖D i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let v : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun i j =>
    C (sphereSobolevRotationL (3/2 : ℝ) i j u) + D i j (I u)
  have hI : ‖I u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using I.le_of_opNorm_le
      (norm_sphereSobolevInclusionL_le (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) u
  have hR (i j : Fin 3) :
      ‖sphereSobolevRotationL (3/2 : ℝ) i j u‖ ≤ Real.sqrt 2 * ‖u‖ :=
    (sphereSobolevRotationL (3/2 : ℝ) i j).le_of_opNorm_le
      (norm_sphereSobolevRotationL_le (3/2 : ℝ) i j) u
  have hz : ‖C (I u)‖ ≤ ‖C‖ * ‖u‖ :=
    (C.le_opNorm (I u)).trans (mul_le_mul_of_nonneg_left hI (norm_nonneg C))
  have hv (i j : Fin 3) : ‖v i j‖ ≤ (‖C‖ * Real.sqrt 2 + ‖D i j‖) * ‖u‖ := by
    calc
      _ ≤ ‖C (sphereSobolevRotationL (3/2 : ℝ) i j u)‖ + ‖D i j (I u)‖ := norm_add_le _ _
      _ ≤ ‖C‖ * ‖sphereSobolevRotationL (3/2 : ℝ) i j u‖ + ‖D i j‖ * ‖I u‖ :=
        add_le_add (C.le_opNorm _) ((D i j).le_opNorm _)
      _ ≤ ‖C‖ * (Real.sqrt 2 * ‖u‖) + ‖D i j‖ * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hR i j) (norm_nonneg C))
          (mul_le_mul_of_nonneg_left hI (norm_nonneg (D i j)))
      _ = _ := by ring
  have hSum : (∑ i : Fin 3, ∑ j : Fin 3, ‖v i j‖) ≤
      (9 * (‖C‖ * Real.sqrt 2) + ∑ i : Fin 3, ∑ j : Fin 3, ‖D i j‖) * ‖u‖ := by
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (‖C‖ * Real.sqrt 2 + ‖D i j‖) * ‖u‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hv i j
      _ = _ := by
        simp_rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    _ ≤ ‖C (I u)‖ + Real.sqrt 2 * ∑ i : Fin 3, ∑ j : Fin 3, ‖v i j‖ := by
      rw [sphereSobolevRotationCommutatorHighLiftL_apply]
      exact norm_sphereSobolevLowerRotationReconstruction_le (C (I u)) v
    _ ≤ ‖C‖ * ‖u‖ + Real.sqrt 2 *
        ((9 * (‖C‖ * Real.sqrt 2) + ∑ i : Fin 3, ∑ j : Fin 3, ‖D i j‖) * ‖u‖) :=
      add_le_add hz (mul_le_mul_of_nonneg_left hSum (Real.sqrt_nonneg 2))
    _ = (‖C‖ + 9 * ‖C‖ * (Real.sqrt 2)^2 +
        Real.sqrt 2 * ∑ i : Fin 3, ∑ j : Fin 3, ‖D i j‖) * ‖u‖ := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

lemma sphereSobolevRotationCommutatorHighLiftL_lower_compatibility
    (C : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (D : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hWitness : ∀ (u : SphereSobolev (3/2 : ℝ)) (i j : Fin 3),
      sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
          (C (sphereSobolevRotationL (3/2 : ℝ) i j u) +
            D i j (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)) =
        sphereSobolevRotationL (-(1/2 : ℝ)) i j
          (C (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u))) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRotationCommutatorHighLiftL C D) =
      C.comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevRotationCommutatorHighLiftL C D u) =
    C (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)
  rw [sphereSobolevRotationCommutatorHighLiftL_apply]
  exact sphereSobolevInclusion_lowerRotationReconstruction _ _ (hWitness u)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationCommutatorHighLiftL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationCommutatorHighLiftL_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevRotationCommutatorHighLiftL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationCommutatorHighLiftL_lower_compatibility
