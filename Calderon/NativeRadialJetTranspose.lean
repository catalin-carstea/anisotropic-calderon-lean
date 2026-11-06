import Calderon.NativeLowerTransposeSignedTaylor
import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.ActualFirstCorrectionSobolevFamilies

/-! Radial jets of the native adjoint: physical k and the genuine
opposite-index radial drift transpose; no PDE/gain/jet premise. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

lemma sphereSobolevShiftedDegree_high_half_compatibility :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevShiftedDegreeL (3/2 : ℝ)) =
    (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  have hBhigh (u : SphereSobolev (3/2 : ℝ)) (k : ℕ) :
      sphereSobolevCoefficientL (1/2 : ℝ) k (sphereSobolevShiftedDegreeL (3/2 : ℝ) u) =
        (k : ℝ) • sphereSobolevCoefficientL (3/2 : ℝ) k u := by
    have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) u))
      (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
    exact hIndex.symm.trans (sphereSobolevCoefficientL_shiftedDegree (3/2 : ℝ) k u)
  have hBlow (u : SphereSobolev (1/2 : ℝ)) (k : ℕ) :
      sphereSobolevCoefficientL (-(1/2 : ℝ)) k (sphereSobolevShiftedDegreeL (1/2 : ℝ) u) =
        (k : ℝ) • sphereSobolevCoefficientL (1/2 : ℝ) k u := by
    have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) u))
      (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
    exact hIndex.symm.trans (sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k u)
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion]
  rw [hBhigh,hBlow,sphereSobolevCoefficientL_inclusion]

lemma sphereLowerDistributionalTranspose_shiftedDegree_half :
    sphereLowerDistributionalTranspose (sphereSobolevShiftedDegreeL (1/2 : ℝ)) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) := by
  have hB (u : SphereSobolev (1/2 : ℝ)) (k : ℕ) :
      sphereSobolevCoefficientL (-(1/2 : ℝ)) k (sphereSobolevShiftedDegreeL (1/2 : ℝ) u) =
        (k : ℝ) • sphereSobolevCoefficientL (1/2 : ℝ) k u := by
    have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) u))
      (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
    exact hIndex.symm.trans (sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k u)
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  calc
    _ = sphereSobolevDualPairing (1/2 : ℝ) u (sphereSobolevShiftedDegreeL (1/2 : ℝ) z) :=
      (sphereSobolevDualPairing_lower_distributionalTranspose
        (sphereSobolevShiftedDegreeL (1/2 : ℝ)) z u).symm
    _ = _ := by
      rw [sphereSobolevDualPairing_eq_tsum,sphereSobolevDualPairing_eq_tsum]
      apply tsum_congr
      intro k
      rw [hB,hB]
      exact (real_inner_smul_right (F := harmonicSphereSubspace k)
        (sphereSobolevCoefficientL (1/2 : ℝ) k u)
        (sphereSobolevCoefficientL (1/2 : ℝ) k z) (k : ℝ)).trans
          ((congrArg (fun t : ℝ => (k : ℝ)*t)
            (real_inner_comm (sphereSobolevCoefficientL (1/2 : ℝ) k u)
              (sphereSobolevCoefficientL (1/2 : ℝ) k z)).symm).trans
                (real_inner_smul_right (F := harmonicSphereSubspace k)
                  (sphereSobolevCoefficientL (1/2 : ℝ) k z)
                  (sphereSobolevCoefficientL (1/2 : ℝ) k u) (k : ℝ)).symm)

lemma sphereLowerDistributionalTranspose_inclusion_radialDrift
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) :
    sphereLowerDistributionalTranspose
      ((sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d)) =
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d) := by
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let A := sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d
  let N := sphereSobolevRadialDriftL hF hO hD (-(1/2 : ℝ)) d
  let D := sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d
  have hSym (u v : SphereSobolev (1/2 : ℝ)) :
      sphereSobolevDualPairing (1/2 : ℝ) u (J v) =
        sphereSobolevDualPairing (1/2 : ℝ) v (J u) := by
    rw [sphereSobolevDualPairing_eq_tsum,sphereSobolevDualPairing_eq_tsum]
    simp only [J,sphereSobolevCoefficientL_inclusion]
    apply tsum_congr
    intro k
    exact real_inner_comm _ _
  have hC (z : SphereSobolev (1/2 : ℝ)) : J (A z) = N (J z) :=
    sphereSobolevInclusionL_radialDrift hF hO hD (1/2 : ℝ) (-(1/2 : ℝ))
      (by norm_num) d z
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  calc
    _ = sphereSobolevDualPairing (1/2 : ℝ) u (J (A z)) :=
      (sphereSobolevDualPairing_lower_distributionalTranspose (J.comp A) z u).symm
    _ = sphereSobolevDualPairing (1/2 : ℝ) u (N (J z)) :=
      congrArg (sphereSobolevDualPairing (1/2 : ℝ) u) (hC z)
    _ = sphereSobolevDualPairing (1/2 : ℝ) (D u) (J z) :=
      (sphereSobolevDualPairing_radialDriftAdjoint hF hO hD (1/2 : ℝ) d u (J z)).symm
    _ = _ := hSym (D u) z

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevShiftedDegree_high_half_compatibility
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_shiftedDegree_half
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_inclusion_radialDrift
