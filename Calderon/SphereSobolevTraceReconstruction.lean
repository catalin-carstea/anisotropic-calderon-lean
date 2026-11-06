import Calderon.SphereSobolevOrderOneRotation
import Calderon.HarmonicSphereRotationCasimirVector

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection SmoothSphereRotationBounds SpectralWeightedGraph
  DirichletFamily.DriftBootstrap

def sphereTraceReconstructionWeight (k : ℕ) : ℝ :=
  (1+(k:ℝ))/(1+(k:ℝ)*((k:ℝ)+1))

lemma sphereTraceReconstructionWeight_nonneg (k : ℕ) :
    0 ≤ sphereTraceReconstructionWeight k := by unfold sphereTraceReconstructionWeight; positivity

lemma sphereTraceReconstructionWeight_le_one (k : ℕ) :
    sphereTraceReconstructionWeight k ≤ 1 := by
  unfold sphereTraceReconstructionWeight
  apply (div_le_iff₀ (by positivity : 0 < 1+(k:ℝ)*((k:ℝ)+1))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma norm_sphereTraceReconstructionRotationBlock_le
    (k : ℕ) (i j : Fin 3) (a : harmonicSphereSubspace k) :
    ‖(-(1/2:ℝ)*sphereTraceReconstructionWeight k) • harmonicSphereRotation k i j a‖ ≤
      Real.sqrt 2 * ‖a‖ := by
  have hd : 0 < 1+(k:ℝ)*((k:ℝ)+1) := by positivity
  have hc := sphereTraceReconstructionWeight_nonneg k
  have hs : (1/2:ℝ)*sphereTraceReconstructionWeight k*(1+(k:ℝ)) ≤ 1 := by
    have he : (1/2:ℝ)*sphereTraceReconstructionWeight k*(1+(k:ℝ)) =
        (1+(k:ℝ))^2/(2*(1+(k:ℝ)*((k:ℝ)+1))) := by
      unfold sphereTraceReconstructionWeight
      field_simp [hd.ne']
      <;> ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2*(1+(k:ℝ)*((k:ℝ)+1)))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hc]
  norm_num
  calc
    (1/2:ℝ)*sphereTraceReconstructionWeight k*‖harmonicSphereRotation k i j a‖ ≤
        ((1/2:ℝ)*sphereTraceReconstructionWeight k)*(Real.sqrt 2*(1+(k:ℝ))*‖a‖) :=
      mul_le_mul_of_nonneg_left (norm_harmonicSphereRotation_le k i j a) (by positivity)
    _ = ((1/2:ℝ)*sphereTraceReconstructionWeight k*(1+(k:ℝ)))*(Real.sqrt 2*‖a‖) := by ring
    _ ≤ 1*(Real.sqrt 2*‖a‖) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = Real.sqrt 2*‖a‖ := one_mul _

def sphereSobolevTraceReconstructionIdentityL :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  lp.mapCLM 2 (fun k => sphereTraceReconstructionWeight k •
    ContinuousLinearMap.id ℝ (harmonicSphereSubspace k)) (by norm_num : 0 ≤ (1:ℝ)) (by
      intro k
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : 0 ≤ (1:ℝ))
      intro a
      rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (sphereTraceReconstructionWeight_nonneg k)]
      exact mul_le_mul_of_nonneg_right (sphereTraceReconstructionWeight_le_one k) (norm_nonneg a))

lemma sphereSobolevTraceReconstructionIdentityL_apply (u : SphereSobolev (1/2:ℝ)) (k : ℕ) :
    sphereSobolevTraceReconstructionIdentityL u k = sphereTraceReconstructionWeight k • u k := rfl

def sphereSobolevTraceReconstructionRotationL (i j : Fin 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  lp.mapCLM 2 (fun k => (-(1/2:ℝ)*sphereTraceReconstructionWeight k) • harmonicSphereRotation k i j)
    (Real.sqrt_nonneg 2) (by
      intro k
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2)
      intro a
      exact norm_sphereTraceReconstructionRotationBlock_le k i j a)

lemma sphereSobolevTraceReconstructionRotationL_apply
    (i j : Fin 3) (u : SphereSobolev (1/2:ℝ)) (k : ℕ) :
    sphereSobolevTraceReconstructionRotationL i j u k =
      (-(1/2:ℝ)*sphereTraceReconstructionWeight k) • harmonicSphereRotation k i j (u k) := rfl

lemma sphereTraceReconstructionBlock_identity (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereTraceReconstructionWeight k • a +
      ∑ i : Fin 3, ∑ j : Fin 3, (-(1/2:ℝ)*sphereTraceReconstructionWeight k) •
        harmonicSphereRotation k i j (harmonicSphereRotation k i j a) = (1+(k:ℝ)) • a := by
  have hInner (i : Fin 3) :
      (∑ j : Fin 3, (-(1/2:ℝ)*sphereTraceReconstructionWeight k) •
        harmonicSphereRotation k i j (harmonicSphereRotation k i j a)) =
      (-(1/2:ℝ)*sphereTraceReconstructionWeight k) •
        ∑ j : Fin 3, harmonicSphereRotation k i j (harmonicSphereRotation k i j a) :=
    by rw [Finset.smul_sum]
  simp_rw [hInner]
  rw [← Finset.smul_sum,sum_harmonicSphereRotation_twice,smul_smul,← add_smul]
  apply congrArg (fun c : ℝ => c • a)
  unfold sphereTraceReconstructionWeight
  have hd : 1+(k:ℝ)*((k:ℝ)+1) ≠ 0 := ne_of_gt (by positivity)
  field_simp [hd]
  <;> ring

lemma sphereSobolevTraceReconstruction_stored
    (u : SphereSobolev (1/2:ℝ)) (v : Fin 3 → Fin 3 → SphereSobolev (1/2:ℝ))
    (hGraph : ∀ i j k, v i j k = harmonicSphereRotation k i j (u k)) (k : ℕ) :
    (sphereSobolevTraceReconstructionIdentityL u +
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)) k =
        (1+(k:ℝ)) • u k := by
  let E : SphereSobolev (3/2:ℝ) →L[ℝ] harmonicSphereSubspace k :=
    lp.evalCLM ℝ (fun n : ℕ => harmonicSphereSubspace n) 2 k
  let a : harmonicSphereSubspace k := u k
  have hIdentity : E (sphereSobolevTraceReconstructionIdentityL u) = sphereTraceReconstructionWeight k • a :=
    sphereSobolevTraceReconstructionIdentityL_apply u k
  have hRotation (i j : Fin 3) : E (sphereSobolevTraceReconstructionRotationL i j (v i j)) =
      (-(1/2:ℝ)*sphereTraceReconstructionWeight k) • harmonicSphereRotation k i j (harmonicSphereRotation k i j a) :=
    (sphereSobolevTraceReconstructionRotationL_apply i j (v i j) k).trans
      (congrArg (fun z : harmonicSphereSubspace k =>
        (-(1/2:ℝ)*sphereTraceReconstructionWeight k) • harmonicSphereRotation k i j z) (hGraph i j k))
  have hPoint : E (sphereSobolevTraceReconstructionIdentityL u +
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)) =
      sphereTraceReconstructionWeight k • a +
        ∑ i : Fin 3, ∑ j : Fin 3, (-(1/2:ℝ)*sphereTraceReconstructionWeight k) •
          harmonicSphereRotation k i j (harmonicSphereRotation k i j a) := by
    rw [E.map_add,hIdentity]
    apply congrArg (fun z : harmonicSphereSubspace k => sphereTraceReconstructionWeight k • a+z)
    calc
      _ = ∑ i : Fin 3, E (∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)) := map_sum E _ _
      _ = ∑ i : Fin 3, ∑ j : Fin 3, E (sphereSobolevTraceReconstructionRotationL i j (v i j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact map_sum E _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hRotation i j
  exact hPoint.trans (sphereTraceReconstructionBlock_identity k a)

lemma besselWeight_threeHalf_reconstruction (k : ℕ) :
    besselWeight (-(3/2:ℝ)) k*(1+(k:ℝ)) = besselWeight (-(1/2:ℝ)) k := by
  unfold besselWeight
  calc
    (1+(k:ℝ)) ^ (-(3/2:ℝ)) * (1+(k:ℝ)) =
        (1+(k:ℝ)) ^ (-(3/2:ℝ)) * (1+(k:ℝ)) ^ (1:ℝ) :=
      congrArg (fun t : ℝ => (1+(k:ℝ)) ^ (-(3/2:ℝ)) * t) (Real.rpow_one (1+(k:ℝ))).symm
    _ = (1+(k:ℝ)) ^ (-(3/2:ℝ)+1) :=
      (Real.rpow_add (by positivity : 0 < 1+(k:ℝ)) (-(3/2:ℝ)) 1).symm
    _ = (1+(k:ℝ)) ^ (-(1/2:ℝ)) := by norm_num

lemma sphereSobolevCoefficientL_traceReconstruction
    (u : SphereSobolev (1/2:ℝ)) (v : Fin 3 → Fin 3 → SphereSobolev (1/2:ℝ))
    (hGraph : ∀ i j k, v i j k = harmonicSphereRotation k i j (u k)) (k : ℕ) :
    sphereSobolevCoefficientL (3/2:ℝ) k
      (sphereSobolevTraceReconstructionIdentityL u +
        ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)) =
      sphereSobolevCoefficientL (1/2:ℝ) k u := by
  change besselWeight (-(3/2:ℝ)) k •
    ((sphereSobolevTraceReconstructionIdentityL u +
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSobolevTraceReconstructionRotationL i j (v i j)) k) =
      besselWeight (-(1/2:ℝ)) k • u k
  rw [sphereSobolevTraceReconstruction_stored u v hGraph k,smul_smul,
    besselWeight_threeHalf_reconstruction]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTraceReconstructionWeight

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTraceReconstructionWeight_nonneg

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTraceReconstructionWeight_le_one

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereTraceReconstructionRotationBlock_le

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevTraceReconstructionIdentityL

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevTraceReconstructionIdentityL_apply

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevTraceReconstructionRotationL

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevTraceReconstructionRotationL_apply

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevTraceReconstruction_stored

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.besselWeight_threeHalf_reconstruction

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_traceReconstruction

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTraceReconstructionBlock_identity
