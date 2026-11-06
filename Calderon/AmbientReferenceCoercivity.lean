import Calderon.AmbientReferenceProfileEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AmbientReferenceCoercivity
open SphereHarmonic SmoothSphereFields SpectralCoreRegularity WeightedSpectralEnergy
  AmbientReferenceRaising AmbientReferenceProfileEnergy HarmonicRaisingModel
  HarmonicProjectedCoercivity CovariantHarmonicEnergy ReferenceDensityBounds RadiusProfile ConformalDepth

def referenceAllModeRaisingEnergy (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) *
    ‖referenceAllModeRaising hF hO hD g hg L lam f G hG x‖^2

def referenceAllModeLoweringEnergy (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) *
    ‖referenceAllModeLowering hF hO hD g hg L lam f G hG x‖^2

def referenceAllModeRaisingCutEnergy (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (n : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) * ‖sphereShiftPartialSum hO hD 2 n
    (referenceAllModeRaising hF hO hD g hg L lam f G hG x)‖^2

def referenceAllModeLoweringCutEnergy (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (n : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) * ‖sphereShiftPartialSum hO hD 0 n
    (referenceAllModeLowering hF hO hD g hg L lam f G hG x)‖^2

theorem referenceAllModeRaisingCutEnergy_eq_sum_modes
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p n : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    referenceAllModeRaisingCutEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L) n G hG =
      ∑ m ∈ Finset.range n, referenceHarmonicRaisingEnergy hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y))
          (referenceLogRadius δ R p L) := by
  have hi (m : ℕ) := (integrable_referenceHarmonicProjection_energies hF hO hD
    g hg lam δ R L p m hδ hR hL hp (ambientSphereL2 G hG)
    (contDiff_ambientSphereL2 G hG) K hK
    (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))).2.1
  unfold referenceAllModeRaisingCutEnergy
  simp_rw [norm_sphereShiftPartialSum_sq,referenceAllModeRaising_coordinate,Finset.mul_sum]
  exact integral_finsetSum _ (fun m _ => hi m)

theorem referenceAllModeLoweringCutEnergy_eq_sum_modes
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p n : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    referenceAllModeLoweringCutEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L) n G hG =
      ∑ m ∈ Finset.range n, referenceHarmonicLoweringEnergy hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y))
          (referenceLogRadius δ R p L) := by
  have hi (m : ℕ) := (integrable_referenceHarmonicProjection_energies hF hO hD
    g hg lam δ R L p m hδ hR hL hp (ambientSphereL2 G hG)
    (contDiff_ambientSphereL2 G hG) K hK
    (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))).2.2
  unfold referenceAllModeLoweringCutEnergy
  simp_rw [norm_sphereShiftPartialSum_sq,Nat.add_zero,referenceAllModeLowering_coordinate,Finset.mul_sum]
  exact integral_finsetSum _ (fun m _ => hi m)

theorem tendsto_referenceAllModeRaisingCutEnergy
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hmean : ∀ x, sphereMean (ambientSphereL2 G hG x)=0) :
    Tendsto (fun n : ℕ => referenceAllModeRaisingCutEnergy hF hO hD g hg L lam f n G hG)
      atTop (𝓝 (referenceAllModeRaisingEnergy hF hO hD g hg L lam f G hG)) := by
  have ht := tendsto_integral_sphereShiftPartialSum_sq g hg L lam hO hD
    (fun _ => 1) continuous_const _
    (contDiff_referenceAllModeRaising hF hO hD g hg L lam f hf G hG).continuous
    (hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam f G hG K hK hz) 2
    (by
      intro x k hk
      have hcase : k=0 ∨ k=1 := by omega
      rcases hcase with rfl | rfl
      · exact referenceAllModeRaising_coordinate_zero hF hO hD g hg L lam f G hG x
      · exact referenceAllModeRaising_coordinate_one_of_meanZero hF hO hD g hg L lam f G hG hmean x)
  simpa only [mul_one, referenceAllModeRaisingCutEnergy, referenceAllModeRaisingEnergy] using ht

theorem tendsto_referenceAllModeLoweringCutEnergy
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Tendsto (fun n : ℕ => referenceAllModeLoweringCutEnergy hF hO hD g hg L lam f n G hG)
      atTop (𝓝 (referenceAllModeLoweringEnergy hF hO hD g hg L lam f G hG)) := by
  have ht := tendsto_integral_sphereShiftPartialSum_sq g hg L lam hO hD
    (fun _ => 1) continuous_const _
    (contDiff_referenceAllModeLowering hF hO hD g hg L lam f hf G hG).continuous
    (hasCompactSupport_referenceAllModeLowering hF hO hD g hg L lam f G hG K hK hz) 0
    (by intro x k hk; omega)
  simpa only [mul_one, referenceAllModeLoweringCutEnergy, referenceAllModeLoweringEnergy] using ht

/-- Genuine all-mode raising gain on actual ambient smooth representatives, with exact N.
The constants precede every cutoff, field, scale and shrinking radius. -/
theorem exists_referenceAllMode_uniform_coercivity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        ∀ (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
          (hD : DenseSphereHarmonics),
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          (∀ x, sphereMean (ambientSphereL2 G hG x)=0) →
          cRaise * referenceAllModeProfileEnergy hO hD g hg lam δ R L p G hG ≤
            referenceAllModeRaisingEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG -
              referenceAllModeLoweringEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L) G hG := by
  obtain ⟨L,cRaise,hL,hcRaise,hgain⟩ :=
    exists_referenceHarmonicProjection_uniform_coercivity g hg K hK
  refine ⟨L,cRaise,hL,hcRaise,?_⟩
  intro ε hε
  obtain ⟨p,hp,R,hR,hprofile,hmode⟩ := hgain ε hε
  refine ⟨p,hp,R,hR,hprofile,?_⟩
  intro hF hO hD lam hlam δ hδ hδ1 G hG hz hmean
  have hU := contDiff_ambientSphereL2 G hG
  have hzero : ∀ x ∉ K, ambientSphereL2 G hG x=0 :=
    fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx)
  have hfinite (n : ℕ) :
      cRaise * referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p n G hG ≤
        referenceAllModeRaisingCutEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L) n G hG -
          referenceAllModeLoweringCutEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L) n G hG := by
    rw [referenceAllModeProfileCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL (by omega) G hG K hK hz,
      referenceAllModeRaisingCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL (by omega) G hG K hK hz,
      referenceAllModeLoweringCutEnergy_eq_sum_modes hF hO hD g hg lam δ R L p n
        hδ hR hL (by omega) G hG K hK hz,
      Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun m _ =>
      hmode hF hO hD lam hlam δ hδ hδ1 m (ambientSphereL2 G hG) hU hzero)
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  exact le_of_tendsto_of_tendsto
    ((tendsto_referenceAllModeProfileCutEnergy hO hD g hg lam δ R L p hδ hR hL
      (by omega) G hG K hK hz hmean).const_mul cRaise)
    ((tendsto_referenceAllModeRaisingCutEnergy hF hO hD g hg L lam _ hf G hG K hK hz hmean).sub
      (tendsto_referenceAllModeLoweringCutEnergy hF hO hD g hg L lam _ hf G hG K hK hz))
    (Filter.Eventually.of_forall hfinite)

end OAI.AnisotropicCalderon.AmbientReferenceCoercivity
