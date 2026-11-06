import Calderon.ActualReferenceGaugeNormalReciprocalRoom
import Calderon.NativeSmoothMultiplierCommonSupportJets

/-! Derivatives of the same actual scalar reciprocal extension. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic SmoothSphereRotation

variable {g : MatrixField} {L : ℝ}
  {Φ : ℝ → (R3 × R3) → ℝ → R3 × R3}
  {a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ}
  {Q : Set (ℝ × (R3 × ℝ))}

def rotationCoefficient (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q) (i j : Fin 3)
    (p : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  p.2 j * smoothMultiplierSpatialDerivative R.scalar i p -
    p.2 i * smoothMultiplierSpatialDerivative R.scalar j p

lemma contDiff_rotationCoefficient (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q) (i j : Fin 3) :
    ContDiff ℝ ∞ (R.rotationCoefficient i j) :=
  (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    (contDiff_smoothMultiplierSpatialDerivative R.scalar R.smooth i)).sub
  (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    (contDiff_smoothMultiplierSpatialDerivative R.scalar R.smooth j))

lemma rotationCoefficient_eq_rotation (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    R.rotationCoefficient i j (p,z) =
      sphereRotationDerivative j i (fun x : R3 => R.scalar (p,x)) z := by
  unfold rotationCoefficient
  rw [smoothMultiplierSpatialDerivative_eq_slice_gradient R.scalar R.smooth i,
    smoothMultiplierSpatialDerivative_eq_slice_gradient R.scalar R.smooth j]
  simp only [MetricVolume.gradient_coordinate,sphereRotationDerivative,rotationVector,
    map_sub,map_smul,smul_eq_mul,MetricVolume.coordinateVector]

lemma rotationCoefficient_support (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ R.spatialSupport) :
    R.rotationCoefficient i j (p,z) = 0 := by
  unfold rotationCoefficient
  rw [smoothMultiplierSpatialDerivative_zero_outside R.scalar R.smooth R.spatialSupport
    R.supportCompact R.zeroOutside i p z hz,
    smoothMultiplierSpatialDerivative_zero_outside R.scalar R.smooth R.spatialSupport
      R.supportCompact R.zeroOutside j p z hz]
  ring

def rotationJets (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (i j : Fin 3) : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (R.rotationCoefficient i j) (R.contDiff_rotationCoefficient i j)
    R.spatialSupport R.supportCompact (R.rotationCoefficient_support i j)

lemma coefficientValue_rotationJets (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (R.rotationJets n i j p) z = R.rotationCoefficient i j (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n (R.rotationCoefficient i j)
    (R.contDiff_rotationCoefficient i j) R.spatialSupport R.supportCompact
      (R.rotationCoefficient_support i j) p z

lemma rotationJets_spatial_derivatives (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (k : Fin (n+1)) (z : R3) :
    (R.rotationJets n i j p).1 k z =
      iteratedFDeriv ℝ k.val (fun x => R.rotationCoefficient i j (p,x)) z :=
  commonSupportCoefficientFamily_jet n (R.rotationCoefficient i j)
    (R.contDiff_rotationCoefficient i j) R.spatialSupport R.supportCompact
      (R.rotationCoefficient_support i j) p k z

lemma contDiff_rotationJets_val (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => (R.rotationJets n i j p).1) :=
  contDiff_commonSupportCoefficientFamily_val n (R.rotationCoefficient i j)
    (R.contDiff_rotationCoefficient i j) R.spatialSupport R.supportCompact
      (R.rotationCoefficient_support i j)

lemma exists_compact_rotationJets_val_bounds (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (i j : Fin 3) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun t => (R.rotationJets n i j t).1) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _ (R.contDiff_rotationJets_val n i j) K hK N

end OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom

#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.rotationCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_rotationCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.rotationCoefficient_eq_rotation
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.rotationCoefficient_support
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.rotationJets
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.coefficientValue_rotationJets
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.rotationJets_spatial_derivatives
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_rotationJets_val
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.exists_compact_rotationJets_val_bounds
