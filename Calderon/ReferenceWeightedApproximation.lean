import Calderon.SmoothAngularApplication
import Calderon.DilatedProfileBeta

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ReferenceWeightedApproximation
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  ConformalDepth RadiusProfile WeightedBaseSpectral
  WeightedAngularConvergence SmoothAngularApplication

def actualReferenceBeta (g : MatrixField) (L lam d R : ℝ) (p : ℕ) : R3 → ℝ :=
  metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
    (fun x => Real.log (referenceRadius d R p L x))

lemma actualReferenceBeta_eq (g : MatrixField) (L lam d R : ℝ) (p : ℕ)
    (hd : 0 < d) (hR : 0 < R) (x : R3) :
    actualReferenceBeta g L lam d R p x =
      ((p : ℝ) * logSlope d (referenceDepth L x)) *
        metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x := by
  unfold actualReferenceBeta
  rw [log_referenceRadius d R p L hd hR]
  exact metricDifferentialNorm_logProfile _ d (Real.log R) p _ x hd
    ((contDiff_referenceDepth L).differentiable (by simp) x)

lemma continuous_actualReferenceBeta (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam d R : ℝ) (p : ℕ) (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) :
    Continuous (actualReferenceBeta g L lam d R p) := by
  have he : actualReferenceBeta g L lam d R p = fun x =>
      ((p : ℝ) * logSlope d (referenceDepth L x)) *
        metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x :=
    funext (actualReferenceBeta_eq g L lam d R p hd hR)
  have hs : Continuous (logSlope d) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_logSlope d t hd).continuousAt)
  have hinc : Continuous (fun x : R3 => (lam,x)) := continuous_const.prodMk continuous_id
  have hb := (contDiff_dilatedReferenceDepth_metricNorm g hg L hL).continuous.comp hinc
  change Continuous (fun x : R3 =>
    metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x) at hb
  rw [he]
  exact (continuous_const.mul (hs.comp (contDiff_referenceDepth L).continuous)).mul hb

lemma actualReferenceBeta_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam d R : ℝ) (p : ℕ) (hL : 0 < L) (hd : 0 < d) (hR : 0 < R)
    (hp : 1 ≤ p) (x : R3) : 0 < actualReferenceBeta g L lam d R p x := by
  rw [actualReferenceBeta_eq g L lam d R p hd hR x]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hmetric : ∀ y, (referenceMetric (dilatedMetric g lam) L y).PosDef :=
    fun y => EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg lam) y
  exact mul_pos (mul_pos hpR (logSlope_pos d _ hd))
    (metricDifferentialNorm_pos _ hmetric _ x
      (fderiv_referenceDepth_ne_zero L (ne_of_gt hL) x))

lemma continuous_weightedAmbientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam d R : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) (hp : 1 ≤ p)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (t : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    Continuous (fun x => actualReferenceBeta g L lam d R p x ^ t • ambientBesselField hO hD s hs G hG x) :=
  ((continuous_actualReferenceBeta g hg L lam d R p hL hd hR).rpow_const
    (fun x => Or.inl (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp x).ne')).smul (contDiff_ambientBesselField hO hD s hs G hG).continuous

lemma hasCompactSupport_weightedAmbientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam d R : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) (hp : 1 ≤ p)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (t : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    HasCompactSupport (fun x => actualReferenceBeta g L lam d R p x ^ t • ambientBesselField hO hD s hs G hG x) :=
  (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz).smul_left
    (f := fun x => actualReferenceBeta g L lam d R p x ^ t)

lemma memLp_weightedAmbientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam d R : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) (hp : 1 ≤ p)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (t : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    MemLp (fun x => actualReferenceBeta g L lam d R p x ^ t • ambientBesselField hO hD s hs G hG x)
      2 (referenceBaseMeasure g L lam) :=
  memLp_referenceBase g hg L lam _
    (continuous_weightedAmbientBesselField g hg L lam d R p hL hd hR hp hO hD s hs t G hG)
    (hasCompactSupport_weightedAmbientBesselField g hg L lam d R p hL hd hR hp hO hD s hs t G hG K hK hz)

theorem tendsto_referenceWeightedAmbientBesselField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam d R : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) (hp : 1 ≤ p)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (t : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    let b := actualReferenceBeta g L lam d R p
    let W := ambientBesselField hO hD s hs G hG
    let hW := contDiff_ambientBesselField hO hD s hs G hG
    let hc := hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz
    let V := W
    let hv := hW.continuous
    let hvc := hc
    let hb := (continuous_actualReferenceBeta g hg L lam d R p hL hd hR).rpow_const
      (fun x => Or.inl (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp x).ne')
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => b x ^ t • sphereHarmonicPartialSum hO hD n (V x))
      (hb.smul ((sphereHarmonicPartialSum hO hD n).continuous.comp hv))
      ((hasCompactSupport_sphereHarmonicPartialSum hO hD n V hvc).smul_left
        (f := fun x => b x ^ t))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => b x ^ t • V x)
        (hb.smul hv) (hvc.smul_left (f := fun x => b x ^ t)))) :=
  tendsto_referenceBaseLift_base_rpow_smul g hg L lam hO hD
    (actualReferenceBeta g L lam d R p)
    (continuous_actualReferenceBeta g hg L lam d R p hL hd hR)
    (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp) t _
    ((contDiff_ambientBesselField hO hD s hs G hG).continuous)
    ((hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz))

theorem tendsto_referenceWeightedPureDerivative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam d R : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) (hp : 1 ≤ p)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (t : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X : R3) :
    let b := actualReferenceBeta g L lam d R p
    let W := ambientBesselField hO hD s hs G hG
    let hW := contDiff_ambientBesselField hO hD s hs G hG
    let hc := hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz
    let V := (fun x => fderiv ℝ W x X)
    let hv := continuous_pureDerivative W hW X
    let hvc := hasCompactSupport_pureDerivative W hc X
    let hb := (continuous_actualReferenceBeta g hg L lam d R p hL hd hR).rpow_const
      (fun x => Or.inl (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp x).ne')
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => b x ^ t • sphereHarmonicPartialSum hO hD n (V x))
      (hb.smul ((sphereHarmonicPartialSum hO hD n).continuous.comp hv))
      ((hasCompactSupport_sphereHarmonicPartialSum hO hD n V hvc).smul_left
        (f := fun x => b x ^ t))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => b x ^ t • V x)
        (hb.smul hv) (hvc.smul_left (f := fun x => b x ^ t)))) :=
  tendsto_referenceBaseLift_base_rpow_smul g hg L lam hO hD
    (actualReferenceBeta g L lam d R p)
    (continuous_actualReferenceBeta g hg L lam d R p hL hd hR)
    (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp) t _
    (continuous_pureDerivative (ambientBesselField hO hD s hs G hG) (contDiff_ambientBesselField hO hD s hs G hG) X)
    (hasCompactSupport_pureDerivative (ambientBesselField hO hD s hs G hG) (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz) X)

theorem tendsto_referenceWeightedSecondPureDerivative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam d R : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hR : 0 < R) (hp : 1 ≤ p)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (t : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X Y : R3) :
    let b := actualReferenceBeta g L lam d R p
    let W := ambientBesselField hO hD s hs G hG
    let hW := contDiff_ambientBesselField hO hD s hs G hG
    let hc := hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz
    let V := (fun x => fderiv ℝ (fun y => fderiv ℝ W y X) x Y)
    let hv := continuous_pureDerivative _ (contDiff_pureDerivative W hW X) Y
    let hvc := hasCompactSupport_pureDerivative _ (hasCompactSupport_pureDerivative W hc X) Y
    let hb := (continuous_actualReferenceBeta g hg L lam d R p hL hd hR).rpow_const
      (fun x => Or.inl (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp x).ne')
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => b x ^ t • sphereHarmonicPartialSum hO hD n (V x))
      (hb.smul ((sphereHarmonicPartialSum hO hD n).continuous.comp hv))
      ((hasCompactSupport_sphereHarmonicPartialSum hO hD n V hvc).smul_left
        (f := fun x => b x ^ t))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => b x ^ t • V x)
        (hb.smul hv) (hvc.smul_left (f := fun x => b x ^ t)))) :=
  tendsto_referenceBaseLift_base_rpow_smul g hg L lam hO hD
    (actualReferenceBeta g L lam d R p)
    (continuous_actualReferenceBeta g hg L lam d R p hL hd hR)
    (actualReferenceBeta_pos g hg L lam d R p hL hd hR hp) t _
    (continuous_pureDerivative _ (contDiff_pureDerivative (ambientBesselField hO hD s hs G hG) (contDiff_ambientBesselField hO hD s hs G hG) X) Y)
    (hasCompactSupport_pureDerivative _ (hasCompactSupport_pureDerivative (ambientBesselField hO hD s hs G hG) (hasCompactSupport_ambientBesselField hO hD s hs G hG K hK hz) X) Y)

end OAI.AnisotropicCalderon.ReferenceWeightedApproximation
