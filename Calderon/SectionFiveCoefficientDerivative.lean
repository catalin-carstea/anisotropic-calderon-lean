import Calderon.SectionFiveErrorBounds
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.SectionFiveErrorForms
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph BaseDensityAdjoint

lemma directionalDeriv_harmonicCoordinate
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (k : ℕ) (i : R3) (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U) (x : R3) :
    directionalDeriv i (fun y => sphereHarmonicCoordinate hO hD k (U y)) x =
      sphereHarmonicCoordinate hO hD k (directionalDeriv i U x) := by
  unfold directionalDeriv
  have hc : HasFDerivAt (fun y => sphereHarmonicCoordinate hO hD k (U y))
      ((sphereHarmonicCoordinate hO hD k).comp (fderiv ℝ U x)) x :=
    (sphereHarmonicCoordinate hO hD k).hasFDerivAt.comp x
      (hU.differentiable (by simp) x).hasFDerivAt
  rw [hc.fderiv]
  rfl

/-- Differentiating a true varying spectral graph retains the coefficient derivative. -/
theorem directionalDeriv_spectral_family
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : R3 → ℕ → ℝ) (i : R3) (U Q : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) (hQ : ContDiff ℝ ∞ Q)
    (hw : ∀ k, ContDiff ℝ ∞ (fun x => w x k))
    (hgraph : ∀ x, (U x,Q x) ∈ spectralGraph hO hD (w x)) (x : R3) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (directionalDeriv i Q x) =
      directionalDeriv i (fun y => w y k) x • sphereHarmonicCoordinate hO hD k (U x) +
        w x k • sphereHarmonicCoordinate hO hD k (directionalDeriv i U x) := by
  have he : (fun y => sphereHarmonicCoordinate hO hD k (Q y)) =
      (fun y => w y k • sphereHarmonicCoordinate hO hD k (U y)) :=
    funext (fun y => hgraph y k)
  have hd := congrArg (fun f : R3 → harmonicSphereSubspace k => directionalDeriv i f x) he
  rw [directionalDeriv_harmonicCoordinate hO hD k i Q hQ x,
    directionalDeriv_smul i (fun y => w y k)
      (fun y => sphereHarmonicCoordinate hO hD k (U y)) (hw k)
      ((sphereHarmonicCoordinate hO hD k).contDiff.comp hU) x,
    directionalDeriv_harmonicCoordinate hO hD k i U hU x] at hd
  exact hd

theorem coefficient_derivative_remainder_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : R3 → ℕ → ℝ) (i : R3) (U Q Qi : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) (hQ : ContDiff ℝ ∞ Q)
    (hw : ∀ k, ContDiff ℝ ∞ (fun x => w x k))
    (hgraph : ∀ x, (U x,Q x) ∈ spectralGraph hO hD (w x))
    (hQi : ∀ x, (directionalDeriv i U x,Qi x) ∈ spectralGraph hO hD (w x)) (x : R3) :
    (U x,directionalDeriv i Q x-Qi x) ∈
      spectralGraph hO hD (fun k => directionalDeriv i (fun y => w y k) x) := by
  intro k
  rw [map_sub,directionalDeriv_spectral_family hO hD w i U Q hU hQ hw hgraph x k,hQi x k]
  simp only [add_sub_cancel_right]

/-- The lower remainder after one IBP has exactly the differentiated density-weight symbol. -/
theorem weighted_coefficient_derivative_remainder_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : R3 → ℕ → ℝ) (i : R3) (h : R3 → ℝ) (U Q Qi : R3 → SphereL2)
    (hh : ContDiff ℝ ∞ h) (hU : ContDiff ℝ ∞ U) (hQ : ContDiff ℝ ∞ Q)
    (hw : ∀ k, ContDiff ℝ ∞ (fun x => w x k))
    (hgraph : ∀ x, (U x,Q x) ∈ spectralGraph hO hD (w x))
    (hQi : ∀ x, (directionalDeriv i U x,Qi x) ∈ spectralGraph hO hD (w x)) (x : R3) :
    (U x,directionalDeriv i (fun y => h y • Q y) x-h x • Qi x) ∈
      spectralGraph hO hD (fun k => directionalDeriv i h x * w x k +
        h x * directionalDeriv i (fun y => w y k) x) := by
  intro k
  rw [directionalDeriv_smul i h Q hh hQ x,map_sub,map_add,map_smul,map_smul,map_smul,
    hgraph x k,directionalDeriv_spectral_family hO hD w i U Q hU hQ hw hgraph x k,hQi x k]
  simp only [smul_add,smul_smul,add_smul]
  abel

lemma directionalDeriv_mul (i : R3) (f g : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    directionalDeriv i (fun y => f y*g y) x =
      directionalDeriv i f x*g x + f x*directionalDeriv i g x := by
  unfold directionalDeriv
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma directionalDeriv_inv (i : R3) (beta : R3 → ℝ)
    (hbeta : ContDiff ℝ ∞ beta) (x : R3) (hpos : 0 < beta x) :
    directionalDeriv i (fun y => (beta y)⁻¹) x =
      -(beta x ^ 2)⁻¹ * directionalDeriv i beta x := by
  unfold directionalDeriv
  have hi : HasFDerivAt (fun y => (beta y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(beta x^2)⁻¹)).comp (fderiv ℝ beta x)) x :=
    (hasDerivAt_inv (ne_of_gt hpos)).hasFDerivAt.comp x
      (hbeta.differentiable (by simp) x).hasFDerivAt
  rw [hi.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

lemma abs_directionalDeriv_inv_le (i : R3) (beta : R3 → ℝ)
    (hbeta : ContDiff ℝ ∞ beta) (x : R3) (hpos : 0 < beta x) (C : ℝ)
    (hderiv : |directionalDeriv i beta x| ≤ C * beta x^2) :
    |directionalDeriv i (fun y => (beta y)⁻¹) x| ≤ C := by
  rw [directionalDeriv_inv i beta hbeta x hpos,abs_mul,abs_neg,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hpos))]
  have h := mul_le_mul_of_nonneg_left hderiv (inv_nonneg.mpr (sq_nonneg (beta x)))
  calc
    _ ≤ (beta x^2)⁻¹ * (C * beta x^2) := h
    _ = C := by field_simp [ne_of_gt hpos]

/-- A scalar coefficient budget deriving, rather than assuming, the whole differentiated symbol. -/
lemma abs_density_weight_derivative_coefficient_le
    (beta mu dmu dinv w dw Cmu Cbeta Cw Cdw b1 b2 : ℝ)
    (hbeta : 1 ≤ beta) (hmu : 0 ≤ mu)
    (hCmu : 0 ≤ Cmu) (hCbeta : 0 ≤ Cbeta) (hCw : 0 ≤ Cw) (hCdw : 0 ≤ Cdw)
    (hb1 : 0 ≤ b1) (hb12 : b1 ≤ b2)
    (hdmu : |dmu| ≤ Cmu*mu) (hdinv : |dinv| ≤ Cbeta)
    (hw : |w| ≤ Cw*b1) (hdw : |dw| ≤ Cdw*beta*b1) :
    |(dmu*beta⁻¹+mu*dinv)*w+mu*beta⁻¹*dw| ≤
      mu*((Cmu+Cbeta)*Cw+Cdw)*b2 := by
  have hpos : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hinv : 0 ≤ beta⁻¹ := inv_nonneg.mpr hpos.le
  have hinvle : beta⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hbeta
  have hweight : |dmu*beta⁻¹+mu*dinv| ≤ mu*(Cmu+Cbeta) := by
    calc
      _ ≤ |dmu*beta⁻¹|+|mu*dinv| := abs_add_le _ _
      _ = |dmu| * beta⁻¹+mu*|dinv| := by rw [abs_mul,abs_mul,abs_of_nonneg hinv,abs_of_nonneg hmu]
      _ ≤ (Cmu*mu)*beta⁻¹+mu*Cbeta := add_le_add
        (mul_le_mul_of_nonneg_right hdmu hinv) (mul_le_mul_of_nonneg_left hdinv hmu)
      _ ≤ Cmu*mu+mu*Cbeta := add_le_add
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hinvle (mul_nonneg hCmu hmu)) le_rfl
      _ = _ := by ring
  have hterm1 : |(dmu*beta⁻¹+mu*dinv)*w| ≤ mu*(Cmu+Cbeta)*Cw*b1 := by
    rw [abs_mul]
    calc
      _ ≤ (mu*(Cmu+Cbeta))*(Cw*b1) :=
        mul_le_mul hweight hw (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hterm2 : |mu*beta⁻¹*dw| ≤ mu*Cdw*b1 := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg hmu hinv)]
    calc
      _ ≤ mu*beta⁻¹*(Cdw*beta*b1) := mul_le_mul_of_nonneg_left hdw (mul_nonneg hmu hinv)
      _ = _ := by field_simp [ne_of_gt hpos]
  calc
    _ ≤ |(dmu*beta⁻¹+mu*dinv)*w|+|mu*beta⁻¹*dw| := abs_add_le _ _
    _ ≤ mu*(Cmu+Cbeta)*Cw*b1+mu*Cdw*b1 := add_le_add hterm1 hterm2
    _ = mu*((Cmu+Cbeta)*Cw+Cdw)*b1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb12 (by positivity)

end OAI.AnisotropicCalderon.SectionFiveErrorForms
