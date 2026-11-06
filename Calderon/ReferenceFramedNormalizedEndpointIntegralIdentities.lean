import Calderon.SmoothReferenceFramedNormalizedEndpoint

/-! These are identities for the same original physical endpoint and actual spatial
Jacobian on the precise original normalization domain. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

theorem hasFDerivAt_referenceFramedNormalizedEndpointIntegral_slice (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1))
    (q : ℝ) (y z : R3) (r : ℝ) (hzero : (Φ q (y,0) 1).1 = y)
    (hfirst : HasFDerivAt (fun a => (Φ q a 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) :
    HasFDerivAt (fun w => referenceFramedNormalizedEndpointIntegral g L Φ (q,((y,r),w)))
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))) z := by
  have heq : (fun w => referenceFramedNormalizedEndpointIntegral g L Φ (q,((y,r),w))) =
      (fun w => referenceFramedNormalizedEndpoint g L Φ (q,((y,r),w))) := by
    funext w
    exact referenceFramedNormalizedEndpointIntegral_eq g hg L Φ hΘ q y w r hzero hfirst
  rw [heq]
  exact hasFDerivAt_referenceFramedNormalizedEndpoint_slice g L Φ q y z r
    (hΘ.comp (contDiff_const.prodMk contDiff_id)) hfirst

theorem fderiv_referenceFramedNormalizedEndpointIntegral_slice (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1))
    (q : ℝ) (y z : R3) (r : ℝ) (hzero : (Φ q (y,0) 1).1 = y)
    (hfirst : HasFDerivAt (fun a => (Φ q a 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) :
    fderiv ℝ (fun w => referenceFramedNormalizedEndpointIntegral g L Φ (q,((y,r),w))) z =
      referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) :=
  (hasFDerivAt_referenceFramedNormalizedEndpointIntegral_slice g hg L Φ hΘ q y z r
    hzero hfirst).fderiv

theorem hasFDerivAt_referenceFramedNormalizedEndpointIntegral_on_domain (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (a : ReferenceEndpointVariables) (ha : a ∈ referenceFramedNormalizationDomain B) :
    HasFDerivAt (fun w => referenceFramedNormalizedEndpointIntegral g L Φ (a.1,((a.2.1.1,a.2.1.2),w)))
      (referenceFramedNormalizedJacobian g L Φ a) a.2.2 := by
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,hvalue,hfirst,_⟩
  exact hasFDerivAt_referenceFramedNormalizedEndpointIntegral_slice g hg L Φ hΘ
    a.1 a.2.1.1 a.2.2 a.2.1.2
    (hvalue a.1 ha.1 a.2.1.1 ha.2) (hfirst a.1 ha.1 a.2.1.1 ha.2)

theorem referenceFramedPhysicalEndpoint_eq_center_add_radius_integral (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1))
    (q : ℝ) (y z : R3) (r : ℝ) (hzero : (Φ q (y,0) 1).1 = y)
    (hfirst : HasFDerivAt (fun a => (Φ q a 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) :
    referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)) =
      y + r • referenceFramedNormalizedEndpointIntegral g L Φ (q,((y,r),z)) := by
  rw [referenceFramedNormalizedEndpointIntegral_eq g hg L Φ hΘ q y z r hzero hfirst]
  exact referenceFramedPhysicalEndpoint_eq_center_add_radius_normalized g L Φ q y z r hzero

theorem referenceFramedPhysicalEndpoint_eq_center_add_radius_integral_on_domain (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (a : ReferenceEndpointVariables) (ha : a ∈ referenceFramedNormalizationDomain B) :
    referenceFramedPhysicalEndpoint g L Φ a =
      a.2.1.1 + a.2.1.2 • referenceFramedNormalizedEndpointIntegral g L Φ a := by
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,hvalue,hfirst,_⟩
  exact referenceFramedPhysicalEndpoint_eq_center_add_radius_integral g hg L Φ hΘ
    a.1 a.2.1.1 a.2.2 a.2.1.2
    (hvalue a.1 ha.1 a.2.1.1 ha.2) (hfirst a.1 ha.1 a.2.1.1 ha.2)

end OAI.AnisotropicCalderon.ConnectionError
