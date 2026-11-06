import Calderon.AmbientReferenceRaising
import Calderon.FourTermProfileEnergy
import Calderon.HarmonicProjectedCoercivity

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AmbientReferenceProfileEnergy
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  SpectralCoreRegularity SpectralWeightedGraph PositiveSpectralCore AmbientReferenceRaising
  WeightedBaseSpectral WeightedSpectralEnergy FourTermProfileEnergy HarmonicProjectedCoercivity
  CovariantHarmonicEnergy SmoothMetricFrame RadiusProfile ReferenceDensityBounds
  WeightedRaisingBounds ConformalDepth

lemma besselWeight_half_sq (k : ℕ) : besselWeight (1/2:ℝ) k^2=1+(k:ℝ) := by
  unfold besselWeight
  rw [← Real.rpow_mul_natCast (by positivity) (1/2:ℝ) 2]
  norm_num

lemma besselWeight_three_half_sq (k : ℕ) :
    besselWeight (3/2:ℝ) k^2=(1+(k:ℝ))^3 := by
  unfold besselWeight
  rw [← Real.rpow_mul_natCast (by positivity) (3/2:ℝ) 2]
  norm_num [Real.rpow_natCast]

lemma ambientBesselField_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (k : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD k (ambientBesselField hO hD s hs G hG x) =
      besselWeight s k • sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x) :=
  ambientBesselField_graph hO hD s hs G hG x k

lemma referenceHorizontalBesselField_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (hs : s ≤ 2) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (k : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (referenceHorizontalBesselField hO hD g hg L lam s hs i G hG x) =
        besselWeight s k • sphereHarmonicCoordinate hO hD k
          (referenceHorizontalField g hg L lam i G hG x) :=
  referenceHorizontalBesselField_graph hO hD g hg L lam s hs i G hG x k

lemma referenceHorizontalField_eq_zero (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (i : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceHorizontalField g hg L lam i G hG x=0 :=
  ambientSphereL2_eq_zero _ (contDiff_referenceHorizontalAmbient g hg L lam i G hG) x
    (referenceHorizontalAmbient_sphere_zero g hg L lam i G hG K hK hz x hx)

lemma referenceHorizontalBesselField_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam s : ℝ) (hs : s ≤ 2) (i : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceHorizontalBesselField hO hD g hg L lam s hs i G hG x=0 :=
  ambientBesselField_eq_zero hO hD s hs _
    (contDiff_referenceHorizontalAmbient g hg L lam i G hG) K
    (referenceHorizontalAmbient_sphere_zero g hg L lam i G hG K hK hz) x hx

lemma referenceHorizontalField_coordinate_zero_of_meanZero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hmean : ∀ x, sphereMean (ambientSphereL2 G hG x)=0) (x : R3) :
    sphereHarmonicCoordinate hO hD 0 (referenceHorizontalField g hg L lam i G hG x)=0 := by
  have hz : (fun y => sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG y)) =
      (fun _ : R3 => (0 : harmonicSphereSubspace 0)) := by
    funext y
    exact (sphereHarmonicCoordinate_zero_eq_zero_iff hO hD _).mpr (hmean y)
  rw [referenceHorizontalField_coordinate,hz]
  simp [referenceHarmonicCovariantDerivative]

/-- Exactly N(phi)^2's four source terms for the actual reference covariant field. -/
def referenceAllModeProfileEnergyDensity (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → ℝ :=
  fourTermEnergyDensity (referenceProfileNorm g lam δ R p L)
    (fun i => referenceHorizontalField g hg L lam i G hG)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun i => referenceHorizontalBesselField hO hD g hg L lam (1/2:ℝ) (by norm_num) i G hG)
    (ambientBesselField hO hD (3/2:ℝ) (by norm_num) G hG)

def referenceAllModeProfileEnergy (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) *
    referenceAllModeProfileEnergyDensity hO hD g hg lam δ R L p G hG x

def referenceAllModeProfileCutDensity (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p n : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → ℝ :=
  fourTermCutDensity hO hD n (referenceProfileNorm g lam δ R p L)
    (fun i => referenceHorizontalField g hg L lam i G hG)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun i => referenceHorizontalBesselField hO hD g hg L lam (1/2:ℝ) (by norm_num) i G hG)
    (ambientBesselField hO hD (3/2:ℝ) (by norm_num) G hG)

def referenceAllModeProfileCutEnergy (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p n : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) *
    referenceAllModeProfileCutDensity hO hD g hg lam δ R L p n G hG x

lemma continuous_referenceAllModeProfileEnergyDensity (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    Continuous (referenceAllModeProfileEnergyDensity hO hD g hg lam δ R L p G hG) :=
  continuous_fourTermEnergyDensity _
    (continuous_referenceProfileNorm g hg lam δ R L p hδ hR)
    (continuous_referenceProfileNorm_inv g hg lam δ R L p hδ hR hL hp) _
    (fun i => (contDiff_referenceHorizontalField g hg L lam i G hG).continuous) _
    (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG).continuous _
    (fun i => (contDiff_referenceHorizontalBesselField hO hD g hg L lam
      (1/2:ℝ) (by norm_num) i G hG).continuous) _
    (contDiff_ambientBesselField hO hD (3/2:ℝ) (by norm_num) G hG).continuous

lemma referenceAllModeProfileEnergyDensity_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceAllModeProfileEnergyDensity hO hD g hg lam δ R L p G hG x=0 :=
  fourTermEnergyDensity_eq_zero _ _ _ _ _ x
    (fun i => referenceHorizontalField_eq_zero g hg L lam i G hG K hK hz x hx)
    (ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx)
    (fun i => referenceHorizontalBesselField_eq_zero hO hD g hg L lam
      (1/2:ℝ) (by norm_num) i G hG K hK hz x hx)
    (ambientBesselField_eq_zero hO hD (3/2:ℝ) (by norm_num) G hG K hz x hx)

theorem integrable_referenceAllModeProfileEnergyDensity (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      referenceAllModeProfileEnergyDensity hO hD g hg lam δ R L p G hG x) :=
  ((continuous_referenceBaseDensity g hg L lam).mul
    (continuous_referenceAllModeProfileEnergyDensity hO hD g hg lam δ R L p hδ hR hL hp G hG)).integrable_of_hasCompactSupport
    ((HasCompactSupport.intro hK (fun x hx =>
      referenceAllModeProfileEnergyDensity_eq_zero hO hD g hg lam δ R L p G hG K hK hz x hx)).mul_left)

lemma referenceAllModeProfileEnergy_nonneg (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    0 ≤ referenceAllModeProfileEnergy hO hD g hg lam δ R L p G hG := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
    (fourTermEnergyDensity_nonneg _ _ _ _ _ x
      (referenceProfileNorm_pos g hg lam δ R L p hδ hR hL hp x).le)

lemma referenceAllModeProfileCutDensity_eq_sum_modes (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p n : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAllModeProfileCutDensity hO hD g hg lam δ R L p n G hG x =
      ∑ m ∈ Finset.range n, referenceHarmonicModeEnergyDensity g lam δ R L p (m+1)
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) x := by
  unfold referenceAllModeProfileCutDensity fourTermCutDensity fourTermEnergyDensity
  simp only [norm_sphereShiftPartialSum_sq]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range n)]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range n)]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [referenceHarmonicModeEnergyDensity]
  simp_rw [ambientBesselField_coordinate,referenceHorizontalBesselField_coordinate,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    besselWeight_half_sq,besselWeight_three_half_sq,referenceHorizontalField_coordinate]
  simp only [besselWeight,Real.rpow_one]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem referenceAllModeProfileCutEnergy_eq_sum_modes
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p n : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p n G hG =
      ∑ m ∈ Finset.range n, referenceHarmonicModeEnergy g lam δ R L p (m+1)
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) := by
  have hi (m : ℕ) := (integrable_referenceHarmonicProjection_energies hF hO hD
    g hg lam δ R L p m hδ hR hL hp (ambientSphereL2 G hG)
    (contDiff_ambientSphereL2 G hG) K hK
    (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))).1
  unfold referenceAllModeProfileCutEnergy
  simp_rw [referenceAllModeProfileCutDensity_eq_sum_modes,Finset.mul_sum]
  exact integral_finsetSum _ (fun m _ => hi m)

theorem tendsto_referenceAllModeProfileCutEnergy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hmean : ∀ x, sphereMean (ambientSphereL2 G hG x)=0) :
    Tendsto (fun n : ℕ => referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p n G hG)
      atTop (𝓝 (referenceAllModeProfileEnergy hO hD g hg lam δ R L p G hG)) := by
  apply tendsto_integral_fourTermCutDensity g hg L lam hO hD _
    (continuous_referenceProfileNorm g hg lam δ R L p hδ hR)
    (fun x => referenceProfileNorm_pos g hg lam δ R L p hδ hR hL hp x) _
    (fun i => (contDiff_referenceHorizontalField g hg L lam i G hG).continuous) _
    (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG).continuous _
    (fun i => (contDiff_referenceHorizontalBesselField hO hD g hg L lam
      (1/2:ℝ) (by norm_num) i G hG).continuous) _
    (contDiff_ambientBesselField hO hD (3/2:ℝ) (by norm_num) G hG).continuous K hK
  · intro x hx
    exact ⟨fun i => referenceHorizontalField_eq_zero g hg L lam i G hG K hK hz x hx,
      ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
      fun i => referenceHorizontalBesselField_eq_zero hO hD g hg L lam
        (1/2:ℝ) (by norm_num) i G hG K hK hz x hx,
      ambientBesselField_eq_zero hO hD (3/2:ℝ) (by norm_num) G hG K hz x hx⟩
  · intro x
    have hU0 := (sphereHarmonicCoordinate_zero_eq_zero_iff hO hD _).mpr (hmean x)
    have hH0 (i : Fin 3) := referenceHorizontalField_coordinate_zero_of_meanZero
      hO hD g hg L lam i G hG hmean x
    refine ⟨hH0,?_,?_,?_⟩
    · rw [ambientBesselField_coordinate,hU0,smul_zero]
    · intro i
      rw [referenceHorizontalBesselField_coordinate,hH0 i,smul_zero]
    · rw [ambientBesselField_coordinate,hU0,smul_zero]

end OAI.AnisotropicCalderon.AmbientReferenceProfileEnergy
