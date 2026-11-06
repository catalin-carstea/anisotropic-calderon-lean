import Calderon.SectionFiveCoefficientDerivative
import Calderon.SectionFiveNormalizedAngularForm
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.SectionFiveErrorForms
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph SpectralWeightComparison BaseDensityAdjoint
  WeightedBaseSpectral ReferenceDensityBounds

lemma directionalDeriv_besselGraph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (i : R3) (U V : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hgraph : ∀ x, (U x,V x) ∈ sphereBesselGraph hO hD s) (x : R3) :
    (directionalDeriv i U x,directionalDeriv i V x) ∈ sphereBesselGraph hO hD s := by
  intro k
  have h := directionalDeriv_spectral_family hO hD (fun _ k => besselWeight s k)
    i U V hU hV (fun _ => contDiff_const) hgraph x k
  simpa only [directionalDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_smul,zero_add] using h

lemma directionalDeriv_clm_apply (i : R3) (K : R3 → SphereL2 →L[ℝ] SphereL2)
    (U : R3 → SphereL2) (hK : ContDiff ℝ ∞ K) (hU : ContDiff ℝ ∞ U) (x : R3) :
    directionalDeriv i (fun y => K y (U y)) x =
      K x (directionalDeriv i U x) + (fderiv ℝ K x i) (U x) := by
  unfold directionalDeriv
  rw [fderiv_clm_apply (hK.differentiable (by simp) x) (hU.differentiable (by simp) x)]
  rfl

lemma norm_bessel_half_le_threehalf
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (u uh ut : SphereL2)
    (hh : (u,uh) ∈ sphereBesselGraph hO hD (1/2))
    (ht : (u,ut) ∈ sphereBesselGraph hO hD (3/2)) : ‖uh‖ ≤ ‖ut‖ := by
  have h := norm_spectralGraph_output_le hO hD (besselWeight (1/2)) (besselWeight (3/2))
    1 (by norm_num) (fun k => by
      rw [abs_of_pos (besselWeight_pos (1/2) k),abs_of_pos (besselWeight_pos (3/2) k),one_mul]
      exact besselWeight_mono (1/2) (3/2) (by norm_num) k) u uh ut hh ht
  simpa only [one_mul] using h

lemma abs_scaled_clm_inner_le (K : SphereL2 →L[ℝ] SphereL2) (d C : ℝ)
    (hK : ‖K‖ ≤ C) (u v : SphereL2) :
    |⟪d • K u,v⟫_ℝ| ≤ (|d| * C) * (‖u‖*‖v‖) := by
  rw [real_inner_smul_left,abs_mul]
  calc
    _ ≤ |d| * (‖K u‖*‖v‖) := mul_le_mul_of_nonneg_left
      (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ ≤ |d| * ((C*‖u‖)*‖v‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((K.le_opNorm u).trans
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _))) (norm_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

/-- Non-diagonal second-base form from a genuine normalized angular operator family and one IBP. -/
theorem compact_normalized_second_error_form_bound
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (directions : ι → R3) (i j : ι) (beta : R3 → ℝ)
    (hbeta : ContDiff ℝ ∞ beta) (hbeta1 : ∀ x, 1 ≤ beta x)
    (phi phiHalf phiOne phiThree q : R3 → SphereL2)
    (hphi : ContDiff ℝ ∞ phi) (hphiHalf : ContDiff ℝ ∞ phiHalf)
    (hq : ContDiff ℝ ∞ q) (hcompact : HasCompactSupport phi)
    (hhalf : ∀ x, (phi x,phiHalf x) ∈ sphereBesselGraph hO hD (1/2))
    (hone : ∀ x, (phi x,phiOne x) ∈ sphereBesselGraph hO hD 1)
    (hthree : ∀ x, (phi x,phiThree x) ∈ sphereBesselGraph hO hD (3/2))
    (K : R3 → SphereL2 →L[ℝ] SphereL2) (hK : ContDiff ℝ ∞ K)
    (hqmap : ∀ x, (q x,K x (phiHalf x)) ∈ sphereBesselGraph hO hD (-(1/2)))
    (Cmu Cbeta Cw Cdw : ℝ)
    (hCmu : 0 ≤ Cmu) (hCbeta : 0 ≤ Cbeta) (hCw : 0 ≤ Cw) (hCdw : 0 ≤ Cdw)
    (hKbound : ∀ x, ‖K x‖ ≤ Cw)
    (hDKbound : ∀ x, ‖(fderiv ℝ K x (directions i))‖ ≤ Cdw * beta x)
    (hdmu : ∀ x, |directionalDeriv (directions i) (fun y => referenceDensityFamily g L (lam,y)) x|
      ≤ Cmu * referenceDensityFamily g L (lam,x))
    (hdbeta : ∀ x, |directionalDeriv (directions i) beta x| ≤ Cbeta * beta x^2)
    (hN : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun k => directionalDeriv (directions k) phi x)
        (phiOne x) (fun k => directionalDeriv (directions k) phiHalf x) (phiThree x))) :
    |epsilon * (∫ x, referenceDensityFamily g L (lam,x) * (beta x)⁻¹ *
      ⟪directionalDeriv (directions i) (directionalDeriv (directions j) phi) x,q x⟫_ℝ)| ≤
      epsilon * (Cw+(Cmu+Cbeta)*Cw+Cdw) *
        sourceNormSquare g L lam beta (fun x k => directionalDeriv (directions k) phi x)
          phiOne (fun x k => directionalDeriv (directions k) phiHalf x) phiThree := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let h : R3 → ℝ := fun x => mu x * (beta x)⁻¹
  let W : R3 → SphereL2 := fun x => K x (phiHalf x)
  let G : R3 → ι → SphereL2 := fun x k => directionalDeriv (directions k) phiHalf x
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k => directionalDeriv (directions k) phi x) (phiOne x) (G x) (phiThree x)
  have hpos (x : R3) : 0 < beta x := lt_of_lt_of_le zero_lt_one (hbeta1 x)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hinv : ContDiff ℝ ∞ (fun x => (beta x)⁻¹) := hbeta.inv (fun x => (hpos x).ne')
  have hh : ContDiff ℝ ∞ h := hmu.mul hinv
  have hW : ContDiff ℝ ∞ W := hK.clm_apply hphiHalf
  have hweighted : ∀ x, (h x • q x,h x • W x) ∈ sphereBesselGraph hO hD (-(1/2)) := by
    intro x
    exact (sphereBesselGraph hO hD (-(1/2))).smul_mem (h x) (hqmap x)
  have hparts := compact_second_form_one_parts (directions i) (directions j) mu
    (fun x => (beta x)⁻¹) phi q hmu hinv hphi hq hcompact
  have hpair (x : R3) :
      ⟪directionalDeriv (directions i) (fun y => h y • q y) x,
        directionalDeriv (directions j) phi x⟫_ℝ =
      ⟪directionalDeriv (directions i) (fun y => h y • W y) x,G x j⟫_ℝ :=
    inner_besselGraph_inverse_pair hO hD (1/2) _ _ _ _
      (directionalDeriv_besselGraph hO hD (-(1/2)) (directions i)
        (fun y => h y • q y) (fun y => h y • W y) (hh.smul hq) (hh.smul hW) hweighted x)
      (directionalDeriv_besselGraph hO hD (1/2) (directions j) phi phiHalf hphi hphiHalf hhalf x)
  have hbound (x : R3) :
      |⟪directionalDeriv (directions i) (fun y => h y • W y) x,G x j⟫_ℝ| ≤
        (Cw+(Cmu+Cbeta)*Cw+Cdw) * (mu x*NN x) := by
    have hmu0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
    have hh0 : 0 ≤ h x := mul_nonneg hmu0 (inv_nonneg.mpr (hpos x).le)
    have hN0 : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
    have hhalfthree := norm_bessel_half_le_threehalf hO hD _ _ _ (hhalf x) (hthree x)
    have hproduct : ‖phiHalf x‖ * ‖G x j‖ ≤ NN x := by
      calc
        _ ≤ ‖phiThree x‖ * ‖G x j‖ := mul_le_mul_of_nonneg_right hhalfthree (norm_nonneg _)
        _ ≤ (beta x)⁻¹ * ‖G x j‖^2 + beta x * ‖phiThree x‖^2 := by
          simpa only [mul_comm] using mul_le_weighted_sq (beta x) ‖G x j‖ ‖phiThree x‖ (hpos x)
        _ ≤ (beta x)⁻¹ * (∑ k, ‖G x k‖^2) + beta x * ‖phiThree x‖^2 :=
          add_le_add (mul_le_mul_of_nonneg_left (norm_sq_le_sum (G x) j)
            (inv_nonneg.mpr (hpos x).le)) le_rfl
        _ ≤ _ := angular_error_terms_le_sourceNormSquareIntegrand (beta x) _ _ _ _
    have hdhinv : |directionalDeriv (directions i) h x| ≤ mu x*(Cmu+Cbeta) := by
      dsimp [h]
      rw [directionalDeriv_mul (directions i) mu (fun y => (beta y)⁻¹) hmu hinv x]
      simpa only [mul_one,mul_zero,add_zero] using abs_density_weight_derivative_coefficient_le
        (beta x) (mu x) (directionalDeriv (directions i) mu x)
        (directionalDeriv (directions i) (fun y => (beta y)⁻¹) x) 1 0 Cmu Cbeta 1 0 1 1
        (hbeta1 x) hmu0 hCmu hCbeta (by norm_num) (by norm_num) (by norm_num) le_rfl
        (hdmu x) (abs_directionalDeriv_inv_le (directions i) beta hbeta x (hpos x) Cbeta (hdbeta x))
        (by norm_num) (by simp)
    have hp : |⟪h x • K x (G x i),G x j⟫_ℝ| ≤ mu x*Cw*NN x := by
      calc
        _ ≤ (|h x| * Cw) * (‖G x i‖*‖G x j‖) := abs_scaled_clm_inner_le (K x) (h x) Cw (hKbound x) _ _
        _ ≤ (|h x| * Cw) * (∑ k, ‖G x k‖^2) := mul_le_mul_of_nonneg_left
          (norm_mul_norm_le_sum (G x) i j) (mul_nonneg (abs_nonneg _) hCw)
        _ = (mu x*Cw) * ((beta x)⁻¹ * (∑ k, ‖G x k‖^2)) := by rw [abs_of_nonneg hh0]; dsimp [h]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (weighted_gradient_square_le_sourceNormSquareIntegrand (beta x) (hpos x).le _ _ _ _)
          (mul_nonneg hmu0 hCw)
    have hm : |⟪directionalDeriv (directions i) h x • K x (phiHalf x),G x j⟫_ℝ| ≤
        (mu x*(Cmu+Cbeta)*Cw)*NN x := by
      calc
        _ ≤ (|directionalDeriv (directions i) h x| * Cw) * (‖phiHalf x‖*‖G x j‖) :=
          abs_scaled_clm_inner_le (K x) _ Cw (hKbound x) _ _
        _ ≤ (mu x*(Cmu+Cbeta)*Cw) * NN x := mul_le_mul
          (mul_le_mul_of_nonneg_right hdhinv hCw) hproduct (by positivity) (by positivity)
    have hd : |⟪h x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| ≤
        (mu x*Cdw)*NN x := by
      calc
        _ ≤ (|h x| * (Cdw*beta x)) * (‖phiHalf x‖*‖G x j‖) :=
          abs_scaled_clm_inner_le ((fderiv ℝ K x (directions i))) (h x) _ (hDKbound x) _ _
        _ = (mu x*Cdw) * (‖phiHalf x‖*‖G x j‖) := by
          rw [abs_of_nonneg hh0]
          dsimp [h]
          field_simp [(hpos x).ne'] <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hproduct (mul_nonneg hmu0 hCdw)
    have hF : directionalDeriv (directions i) (fun y => h y • W y) x =
        h x • K x (G x i) + directionalDeriv (directions i) h x • K x (phiHalf x) +
          h x • (fderiv ℝ K x (directions i)) (phiHalf x) := by
      rw [directionalDeriv_smul (directions i) h W hh hW x]
      change directionalDeriv (directions i) h x • K x (phiHalf x) +
        h x • directionalDeriv (directions i) (fun y => K y (phiHalf y)) x = _
      rw [directionalDeriv_clm_apply (directions i) K phiHalf hK hphiHalf x,smul_add]
      dsimp [G]
      abel
    rw [hF,inner_add_left,inner_add_left]
    calc
      _ ≤ |⟪h x • K x (G x i),G x j⟫_ℝ +
          ⟪directionalDeriv (directions i) h x • K x (phiHalf x),G x j⟫_ℝ| +
          |⟪h x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| := abs_add_le _ _
      _ ≤ (|⟪h x • K x (G x i),G x j⟫_ℝ| +
          |⟪directionalDeriv (directions i) h x • K x (phiHalf x),G x j⟫_ℝ|) +
          |⟪h x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (mu x*Cw*NN x+(mu x*(Cmu+Cbeta)*Cw)*NN x)+(mu x*Cdw)*NN x :=
        add_le_add (add_le_add hp hm) hd
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (f := fun x => ⟪directionalDeriv (directions i) (fun y => h y • W y) x,G x j⟫_ℝ)
    (hN.const_mul (Cw+(Cmu+Cbeta)*Cw+Cdw))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,mu,NN,G] using hbound x))
  rw [integral_const_mul] at hint
  have hresult : |∫ x, mu x * (beta x)⁻¹ *
      ⟪directionalDeriv (directions i) (directionalDeriv (directions j) phi) x,q x⟫_ℝ| ≤
      (Cw+(Cmu+Cbeta)*Cw+Cdw) * sourceNormSquare g L lam beta
        (fun x k => directionalDeriv (directions k) phi x) phiOne G phiThree := by
    rw [hparts,abs_neg]
    change |∫ x, ⟪directionalDeriv (directions i) (fun y => h y • q y) x,
      directionalDeriv (directions j) phi x⟫_ℝ| ≤ _
    simp_rw [hpair]
    rw [sourceNormSquare_eq_density_integral g hg L lam]
    simpa only [Real.norm_eq_abs,mu,NN,G] using hint
  rw [abs_mul,abs_of_nonneg hepsilon]
  simpa only [G,mul_assoc] using mul_le_mul_of_nonneg_left hresult hepsilon

end OAI.AnisotropicCalderon.SectionFiveErrorForms
