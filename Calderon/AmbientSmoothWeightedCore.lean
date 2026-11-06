import Calderon.AngularWeightedCore
import Calderon.SmoothAmbientAngularCasimir
import Calderon.SpectralWeightComparison
import Calderon.SmoothMovingFrameFields

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AmbientSmoothWeightedCore
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph SpectralWeightComparison
  SmoothSphereFields SmoothAmbientAngularCasimir SmoothMovingFrameFields
  AngularShiftGraph AngularWeightedCore

/-- The exact natural Bessel weight is dominated by enough true Casimir iterates. -/
lemma besselWeight_nat_le_casimirWeight_pow (n k : ℕ) :
    |besselWeight (n:ℝ) k| ≤ |casimirWeight k ^ n| := by
  rw [abs_of_pos (besselWeight_pos (n:ℝ) k),
    abs_of_nonneg (pow_nonneg (casimirWeight_pos k).le n)]
  change (1+(k:ℝ)) ^ (n:ℝ) ≤ casimirWeight k ^ n
  rw [Real.rpow_natCast]
  apply pow_le_pow_left₀ (by positivity) _ n
  unfold casimirWeight
  nlinarith [sq_nonneg (k:ℝ)]

/-- The graph output is an actual smooth field formed from angular derivatives. -/
lemma ambientSphereL2_mem_casimirPowerGraph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (m : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,
      ambientSphereL2 (ambientShiftedAngularCasimirIterate m G)
        (contDiff_ambientShiftedAngularCasimirIterate m G hG) x) ∈
      spectralGraph hO hD (fun k => casimirWeight k ^ m) := by
  intro k
  simpa only [casimirWeight] using
    sphereHarmonicCoordinate_angularCasimirLift hO hD m k G hG x

/-- Bessel outputs are reconstructed from a proved graph pair, with no decay premise. -/
lemma hasSphereBesselWeight_ambientSphereL2 (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    hasSphereBesselWeight hO hD (n:ℝ) (ambientSphereL2 G hG x) := by
  have hw : ∀ k : ℕ, |besselWeight (n:ℝ) k| ≤ 1 * |casimirWeight k ^ n| :=
    fun k => by simpa only [one_mul] using besselWeight_nat_le_casimirWeight_pow n k
  exact exists_spectralGraph_of_weight_le hO hD (besselWeight (n:ℝ))
    (fun k => casimirWeight k ^ n) 1 (by norm_num) hw (ambientSphereL2 G hG x)
    (ambientSphereL2 (ambientShiftedAngularCasimirIterate n G)
      (contDiff_ambientShiftedAngularCasimirIterate n G hG) x)
    (ambientSphereL2_mem_casimirPowerGraph hO hD n G hG x)

lemma norm_besselOutput_ambientSphereL2_le_angularCasimirLift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (n : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) (b : SphereL2)
    (hb : (ambientSphereL2 G hG x,b) ∈ sphereBesselGraph hO hD (n:ℝ)) :
    ‖b‖ ≤ ‖ambientSphereL2 (ambientShiftedAngularCasimirIterate n G)
      (contDiff_ambientShiftedAngularCasimirIterate n G hG) x‖ := by
  have hw : ∀ k : ℕ, |besselWeight (n:ℝ) k| ≤ 1 * |casimirWeight k ^ n| :=
    fun k => by simpa only [one_mul] using besselWeight_nat_le_casimirWeight_pow n k
  simpa only [one_mul] using
    norm_spectralGraph_output_le hO hD (besselWeight (n:ℝ))
      (fun k => casimirWeight k ^ n) 1 (by norm_num) hw
      (ambientSphereL2 G hG x) b
      (ambientSphereL2 (ambientShiftedAngularCasimirIterate n G)
        (contDiff_ambientShiftedAngularCasimirIterate n G hG) x) hb
      (ambientSphereL2_mem_casimirPowerGraph hO hD n G hG x)

/-- Forward smooth-to-core membership for a genuine ambient smooth representative. -/
lemma ambientSphereL2_mem_sphereSmoothWeightedCore (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 G hG x ∈ sphereSmoothWeightedCore hO hD := by
  intro n
  exact hasSphereBesselWeight_ambientSphereL2 hO hD n G hG x

lemma ambientSphereL2_derivative_mem_sphereSmoothWeightedCore (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ∃ du : SphereL2, (ambientSphereL2 G hG x,du) ∈ sphereDerivativeGraph hF hO hD i ∧
      du ∈ sphereSmoothWeightedCore hO hD :=
  sphereSmoothWeightedCore_derivative hF hO hD i (ambientSphereL2 G hG x)
    (ambientSphereL2_mem_sphereSmoothWeightedCore hO hD G hG x)

lemma ambientSphereL2_raising_mem_sphereSmoothWeightedCore (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ∃ ru : SphereL2, (ambientSphereL2 G hG x,ru) ∈ sphereRaisingGraph hF hO hD i ∧
      ru ∈ sphereSmoothWeightedCore hO hD :=
  sphereSmoothWeightedCore_raising hF hO hD i (ambientSphereL2 G hG x)
    (ambientSphereL2_mem_sphereSmoothWeightedCore hO hD G hG x)

/-- The actual base derivative is eligible for the same angular operators. -/
lemma fderiv_ambientSphereL2_mem_sphereSmoothWeightedCore (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    fderiv ℝ (ambientSphereL2 G hG) x (X x) ∈ sphereSmoothWeightedCore hO hD := by
  rw [← ambientSphereL2_baseDirectional X hX G hG x]
  exact ambientSphereL2_mem_sphereSmoothWeightedCore hO hD (ambientBaseDirectional X G)
    (contDiff_ambientBaseDirectional X hX G hG) x

lemma frameHorizontalLift_mem_sphereSmoothWeightedCore (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (C : R3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x => C x i j)) (X : R3 → R3)
    (hX : ContDiff ℝ ∞ X) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 (ambientFrameHorizontal C X G)
      (contDiff_ambientFrameHorizontal C hC X hX G hG) x ∈ sphereSmoothWeightedCore hO hD :=
  ambientSphereL2_mem_sphereSmoothWeightedCore hO hD (ambientFrameHorizontal C X G)
    (contDiff_ambientFrameHorizontal C hC X hX G hG) x

end OAI.AnisotropicCalderon.AmbientSmoothWeightedCore
