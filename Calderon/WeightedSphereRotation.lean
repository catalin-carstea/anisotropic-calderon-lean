import Calderon.AngularWeightedCore
import Calderon.SmoothSphereRotationBounds
import Calderon.SmoothMovingFrameFields
import Calderon.AmbientSmoothWeightedCore
import Calderon.SmoothAngularApplication

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.WeightedSphereRotation
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularWeightedCore
  SmoothSphereRotationBounds SmoothSphereRotationProjection SmoothMovingFrameFields
  SmoothSphereFields SmoothAmbientAngularCasimir AmbientSmoothWeightedCore SmoothAngularApplication

lemma besselWeight_add_one (s : ℝ) (k : ℕ) :
    besselWeight (s+1) k = besselWeight s k * (1+(k:ℝ)) := by
  unfold besselWeight
  rw [Real.rpow_add (by positivity), Real.rpow_one]

/-- Rotation preserves degree, so no shift or zero-mode truncation is used. -/
lemma weighted_sq_harmonicSphereRotation_le (s : ℝ) (k : ℕ) (i j : Fin 3)
    (v : harmonicSphereSubspace k) :
    besselWeight s k^2 * ‖harmonicSphereRotation k i j v‖^2 ≤
      2 * (besselWeight (s+1) k^2 * ‖v‖^2) := by
  have hk : (k:ℝ)*((k:ℝ)+1) ≤ (1+(k:ℝ))^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hc : ‖harmonicSphereRotation k i j v‖^2 ≤
      2*(1+(k:ℝ))^2*‖v‖^2 :=
    (norm_harmonicSphereRotation_sq_le k i j v).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [hk]) (sq_nonneg ‖v‖))
  calc
    _ ≤ besselWeight s k^2 * (2*(1+(k:ℝ))^2*‖v‖^2) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = 2*((besselWeight s k * (1+(k:ℝ)))^2*‖v‖^2) := by ring
    _ = _ := by rw [besselWeight_add_one]

/-- A genuine weighted rotation output is bounded through its exact coordinates. -/
lemma norm_sq_weighted_rotation_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (i j : Fin 3)
    (u wu ru wru : SphereL2)
    (hwu : (u,wu) ∈ sphereBesselGraph hO hD (s+1))
    (hru : ∀ k, sphereHarmonicCoordinate hO hD k ru =
      harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k u))
    (hwru : (ru,wru) ∈ sphereBesselGraph hO hD s) :
    ‖wru‖^2 ≤ 2 * ‖wu‖^2 := by
  have hu := (hasSphereBesselWeight_iff_summable hO hD (s+1) u).mp ⟨wu,hwu⟩
  have hr := (hasSphereBesselWeight_iff_summable hO hD s ru).mp ⟨wru,hwru⟩
  have hbound := hr.tsum_le_tsum
    (fun k => by
      rw [hru k]
      exact weighted_sq_harmonicSphereRotation_le s k i j
        (sphereHarmonicCoordinate hO hD k u)) (hu.mul_left (2:ℝ))
  rw [norm_sq_sphereBesselGraph_output hO hD s ru wru hwru,
    norm_sq_sphereBesselGraph_output hO hD (s+1) u wu hwu]
  simpa only [tsum_mul_left] using hbound

lemma norm_weighted_rotation_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (i j : Fin 3)
    (u wu ru wru : SphereL2)
    (hwu : (u,wu) ∈ sphereBesselGraph hO hD (s+1))
    (hru : ∀ k, sphereHarmonicCoordinate hO hD k ru =
      harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k u))
    (hwru : (ru,wru) ∈ sphereBesselGraph hO hD s) :
    ‖wru‖ ≤ Real.sqrt 2 * ‖wu‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num)]
  exact norm_sq_weighted_rotation_le hO hD s i j u wu ru wru hwu hru hwru

/-- The needed graphs and actual rotation are constructed on the smooth ambient core. -/
lemma norm_sq_ambient_weighted_rotation_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 1) (i j : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖ambientBesselField hO hD s (by linarith)
        (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x‖^2 ≤
      2 * ‖ambientBesselField hO hD (s+1) (by linarith) G hG x‖^2 :=
  norm_sq_weighted_rotation_le hO hD s i j
    (ambientSphereL2 G hG x)
    (ambientBesselField hO hD (s+1) (by linarith) G hG x)
    (ambientSphereL2 (ambientAngularRotation i j G)
      (contDiff_ambientAngularRotation i j G hG) x)
    (ambientBesselField hO hD s (by linarith) (ambientAngularRotation i j G)
      (contDiff_ambientAngularRotation i j G hG) x)
    (ambientBesselField_graph hO hD (s+1) (by linarith) G hG x)
    (fun k => sphereHarmonicCoordinate_ambientAngularRotation hO hD k i j G hG x)
    (ambientBesselField_graph hO hD s (by linarith) (ambientAngularRotation i j G)
      (contDiff_ambientAngularRotation i j G hG) x)

end OAI.AnisotropicCalderon.WeightedSphereRotation
