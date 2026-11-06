import Calderon.ActualCenteredNativeCover
import Calderon.ActualReferenceBetaRadiusBudget
import Calderon.ActualFiniteHarmonicCoreScalar
import Calderon.ActualFiniteCoreSobolevLift
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Manifold
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- A finite smooth partition is fixed on the early closed cylinder, with compact
local supports strictly inside the chosen native packets. -/
theorem exists_native_cover_smooth_partition
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (hCenter : ∀ i : Fin cover.count, ∀ y ∈ (cover.packet i).centers,
      ‖y - (cover.packet i).y0‖ < (cover.packet i).rho) :
    ∃ theta : Fin cover.count → R3 → ℝ,
      (∀ i, ContDiff ℝ ∞ (theta i)) ∧
      (∀ i x, 0 ≤ theta i x ∧ theta i x ≤ 1) ∧
      (∀ x ∈ cylinder, ∑ i, theta i x = 1) ∧
      (∀ x : R3, ∑ i, theta i x ≤ 1) ∧
      (∀ i, tsupport (theta i) ⊆ (cover.packet i).centers) ∧
      (∀ i, HasCompactSupport (theta i)) ∧
      ∀ i, IsCompact (tsupport (theta i) ∩ cylinder) ∧
        tsupport (theta i) ∩ cylinder ⊆ Metric.ball (cover.packet i).y0 (cover.packet i).rho := by
  classical
  have hCover : cylinder ⊆ ⋃ i : Fin cover.count, (cover.packet i).centers := by
    intro x hx
    obtain ⟨i, hi⟩ := cover.covers_cylinder x hx
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, R3))
    isCompact_native_center_cylinder.isClosed
    (fun i : Fin cover.count => (cover.packet i).centers)
    (fun i => (cover.packet i).centers_open) hCover
  let theta : Fin cover.count → R3 → ℝ := fun i x => f i x
  have hSmooth (i : Fin cover.count) : ContDiff ℝ ∞ (theta i) :=
    (f i).contMDiff.contDiff
  have hSub (i : Fin cover.count) : tsupport (theta i) ⊆ (cover.packet i).centers := hf i
  have hCompact (i : Fin cover.count) : HasCompactSupport (theta i) := by
    apply (isCompact_closedBall (cover.packet i).y0 (cover.packet i).rho).of_isClosed_subset
      (isClosed_tsupport (theta i))
    intro x hx
    have hRoom := hCenter i x (hSub i hx)
    simpa only [mem_closedBall, dist_eq_norm] using hRoom.le
  refine ⟨theta, hSmooth, ?_, ?_, ?_, hSub, hCompact, ?_⟩
  · intro i x
    exact ⟨f.nonneg i x, f.le_one i x⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one hx
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using f.sum_le_one x
  · intro i
    constructor
    · exact isCompact_native_center_cylinder.of_isClosed_subset
        ((isClosed_tsupport (theta i)).inter isCompact_native_center_cylinder.isClosed)
        inter_subset_right
    · intro x hx
      have hRoom := hCenter i x (hSub i hx.1)
      simpa only [mem_ball, dist_eq_norm] using hRoom

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity

/-- Spatial scalar multiplication commutes with the actual finite-input Sobolev lift. -/
lemma finiteCoreSobolevLift_coreScalar
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (theta : R3 → ℝ) (hTheta : ContDiff ℝ ∞ theta)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreSobolevLift hO hD s (coreScalar hO hD theta hTheta F) x =
      theta x • finiteCoreSobolevLift hO hD s F x := by
  apply sphereSobolev_ext s
  intro k
  calc
    sphereSobolevCoefficientL s k
        (finiteCoreSobolevLift hO hD s (coreScalar hO hD theta hTheta F) x) =
        sphereHarmonicCoordinate hO hD k ((coreScalar hO hD theta hTheta F).val x) :=
      sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD s _ x k
    _ = theta x • sphereHarmonicCoordinate hO hD k (F.val x) := by
      change sphereHarmonicCoordinate hO hD k (theta x • F.val x) = _
      exact map_smul (sphereHarmonicCoordinate hO hD k) (theta x) (F.val x)
    _ = sphereSobolevCoefficientL s k (theta x • finiteCoreSobolevLift hO hD s F x) := by
      rw [map_smul, sphereSobolevCoefficientL_finiteCoreSobolevLift]

/-- A spatial scalar cutoff preserves the original pointwise spherical mean-zero input. -/
lemma mean_zero_coreScalar
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (theta : R3 → ℝ) (hTheta : ContDiff ℝ ∞ theta)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hMean : ∀ x, sphereMean (F.val x) = 0) :
    ∀ x, sphereMean ((coreScalar hO hD theta hTheta F).val x) = 0 := by
  intro x
  change sphereMean (theta x • F.val x) = 0
  rw [map_smul, hMean x, smul_zero]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
