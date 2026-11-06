import Calderon.SectionFiveNormalizedSecondForm
import Calderon.ActualPrincipalErrorForm

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.LocalizedPrincipalSecondForm
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph SectionFiveErrorForms BaseDensityAdjoint ReferenceDensityBounds
  PrincipalCommutator NaturalAngularAdjoint AngularShiftGraph

/-- A genuine spectral output cannot acquire base support beyond its input. -/
lemma tsupport_besselGraph_subset
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (U V : R3 → SphereL2)
    (hgraph : ∀ x, (U x,V x) ∈ sphereBesselGraph hO hD s) :
    tsupport V ⊆ tsupport U := by
  apply closure_minimal _ (isClosed_tsupport U)
  intro x hx
  change V x ≠ 0 at hx
  by_contra hnot
  have hu : U x = 0 := image_eq_zero_of_notMem_tsupport hnot
  have hv : V x = 0 := spectralGraph_zero_input hO hD (besselWeight s) (V x)
    (by simpa only [sphereBesselGraph, hu] using hgraph x)
  exact hx hv

lemma directionalDeriv_eq_zero_of_notMem_tsupport (X : R3) (U : R3 → SphereL2)
    (x : R3) (hx : x ∉ tsupport U) : directionalDeriv X U x = 0 := by
  unfold directionalDeriv
  rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
  rfl

/-- Actual compact density/inverse jets give a relative density derivative bound on K only. -/
theorem exists_reference_density_relative_first_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ Cmu : ℝ, 0 < Cmu ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      |directionalDeriv (coordinateDirection i)
        (fun y => referenceDensityFamily g L (lam,y)) x| ≤
        Cmu * referenceDensityFamily g L (lam,x) := by
  obtain ⟨M,hM,hbound⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  refine ⟨M^2,by positivity,?_⟩
  intro lam hlam x hx i
  let mu := referenceDensityFamily g L (lam,x)
  have hpos : 0 < mu := referenceDensityFamily_pos g hg L (lam,x)
  have hinv : |mu⁻¹| ≤ M := hbound lam hlam x hx (.inl 1) (.inl ())
  have hfirst : |directionalDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g L (lam,y)) x| ≤ M :=
    hbound lam hlam x hx (.inl 0) (.inr (.inl i))
  have hm : 1 ≤ M*mu := by
    have ht := mul_le_mul_of_nonneg_right hinv hpos.le
    simpa only [abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ hpos.ne'] using ht
  calc
    _ ≤ M := hfirst
    _ ≤ M^2*mu := by
      have ht := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ M)
      simpa only [mul_one,pow_two,mul_assoc] using ht

/-- One unnormalized IBP. All geometry/operator bounds are local to K, and beta is not
differentiated. The graph-map assumption is realized by actual raising fields below. -/
theorem compact_unscaled_second_error_form_bound
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (directions : ι → R3) (i j : ι) (beta : R3 → ℝ) (S : Set R3)
    (hbeta1 : ∀ x ∈ S, 1 ≤ beta x)
    (phi phiHalf phiOne phiThree q : R3 → SphereL2)
    (hphi : ContDiff ℝ ∞ phi) (hphiHalf : ContDiff ℝ ∞ phiHalf)
    (hq : ContDiff ℝ ∞ q) (hcompact : HasCompactSupport phi)
    (hsupport : tsupport phi ⊆ S)
    (hhalf : ∀ x, (phi x,phiHalf x) ∈ sphereBesselGraph hO hD (1/2))
    (hone : ∀ x, (phi x,phiOne x) ∈ sphereBesselGraph hO hD 1)
    (hthree : ∀ x, (phi x,phiThree x) ∈ sphereBesselGraph hO hD (3/2))
    (K : R3 → SphereL2 →L[ℝ] SphereL2) (hK : ContDiff ℝ ∞ K)
    (hqmap : ∀ x, (q x,K x (phiHalf x)) ∈ sphereBesselGraph hO hD (-(1/2)))
    (Cmu Cw Cdw : ℝ) (hCmu : 0 ≤ Cmu) (hCw : 0 ≤ Cw) (hCdw : 0 ≤ Cdw)
    (hKbound : ∀ x ∈ S, ‖K x‖ ≤ Cw*epsilon/beta x)
    (hDKbound : ∀ x ∈ S, ‖fderiv ℝ K x (directions i)‖ ≤ Cdw*epsilon)
    (hdmu : ∀ x ∈ S, |directionalDeriv (directions i)
      (fun y => referenceDensityFamily g L (lam,y)) x| ≤
      Cmu * referenceDensityFamily g L (lam,x))
    (hN : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun k => directionalDeriv (directions k) phi x)
        (phiOne x) (fun k => directionalDeriv (directions k) phiHalf x) (phiThree x))) :
    |∫ x, referenceDensityFamily g L (lam,x) *
      ⟪directionalDeriv (directions i) (directionalDeriv (directions j) phi) x,q x⟫_ℝ| ≤
      (Cw+Cmu*Cw+Cdw)*epsilon *
        sourceNormSquare g L lam beta (fun x k => directionalDeriv (directions k) phi x)
          phiOne (fun x k => directionalDeriv (directions k) phiHalf x) phiThree := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let W : R3 → SphereL2 := fun x => K x (phiHalf x)
  let G : R3 → ι → SphereL2 := fun x k => directionalDeriv (directions k) phiHalf x
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k => directionalDeriv (directions k) phi x) (phiOne x) (G x) (phiThree x)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hW : ContDiff ℝ ∞ W := hK.clm_apply hphiHalf
  have hweighted : ∀ x, (mu x • q x,mu x • W x) ∈ sphereBesselGraph hO hD (-(1/2)) :=
    fun x => (sphereBesselGraph hO hD (-(1/2))).smul_mem (mu x) (hqmap x)
  have hparts := compact_second_form_one_parts (directions i) (directions j) mu
    (fun _ => (1:ℝ)) phi q hmu contDiff_const hphi hq hcompact
  simp only [mul_one] at hparts
  have hpair (x : R3) :
      ⟪directionalDeriv (directions i) (fun y => mu y • q y) x,
        directionalDeriv (directions j) phi x⟫_ℝ =
      ⟪directionalDeriv (directions i) (fun y => mu y • W y) x,G x j⟫_ℝ :=
    inner_besselGraph_inverse_pair hO hD (1/2) _ _ _ _
      (directionalDeriv_besselGraph hO hD (-(1/2)) (directions i)
        (fun y => mu y • q y) (fun y => mu y • W y)
        (hmu.smul hq) (hmu.smul hW) hweighted x)
      (directionalDeriv_besselGraph hO hD (1/2) (directions j)
        phi phiHalf hphi hphiHalf hhalf x)
  have hbound (x : R3) :
      |⟪directionalDeriv (directions i) (fun y => mu y • W y) x,G x j⟫_ℝ| ≤
        ((Cw+Cmu*Cw+Cdw)*epsilon) * (mu x*NN x) := by
    by_cases hx : x ∈ S
    · have hb : 0 < beta x := lt_of_lt_of_le zero_lt_one (hbeta1 x hx)
      have hmu0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
      have hN0 : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) hb.le _ _ _ _
      have hproduct : ‖phiHalf x‖ * ‖G x j‖ ≤ NN x := by
        calc
          _ ≤ ‖phiThree x‖*‖G x j‖ := mul_le_mul_of_nonneg_right
            (norm_bessel_half_le_threehalf hO hD _ _ _ (hhalf x) (hthree x)) (norm_nonneg _)
          _ ≤ (beta x)⁻¹*‖G x j‖^2 + beta x*‖phiThree x‖^2 := by
            simpa only [mul_comm] using mul_le_weighted_sq (beta x) ‖G x j‖ ‖phiThree x‖ hb
          _ ≤ (beta x)⁻¹*(∑ k, ‖G x k‖^2) + beta x*‖phiThree x‖^2 :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_sq_le_sum (G x) j)
              (inv_nonneg.mpr hb.le)) le_rfl
          _ ≤ _ := angular_error_terms_le_sourceNormSquareIntegrand (beta x) _ _ _ _
      have hp : |⟪mu x • K x (G x i),G x j⟫_ℝ| ≤ mu x*Cw*epsilon*NN x := by
        calc
          _ ≤ (|mu x| * (Cw*epsilon/beta x))*(‖G x i‖*‖G x j‖) :=
            abs_scaled_clm_inner_le (K x) (mu x) _ (hKbound x hx) _ _
          _ ≤ (|mu x| * (Cw*epsilon/beta x))*(∑ k, ‖G x k‖^2) :=
            mul_le_mul_of_nonneg_left (norm_mul_norm_le_sum (G x) i j) (by positivity)
          _ = (mu x*Cw*epsilon)*((beta x)⁻¹*(∑ k, ‖G x k‖^2)) := by
            rw [abs_of_nonneg hmu0]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (weighted_gradient_square_le_sourceNormSquareIntegrand (beta x) hb.le _ _ _ _)
            (by positivity)
      have hKweak : ‖K x‖ ≤ Cw*epsilon := (hKbound x hx).trans
        (ActualPrincipalErrorCoefficient.div_le_self_of_one_le _ _
          (mul_nonneg hCw hepsilon) (hbeta1 x hx))
      have hm : |⟪directionalDeriv (directions i) mu x • K x (phiHalf x),G x j⟫_ℝ| ≤
          (mu x*Cmu*Cw*epsilon)*NN x := by
        calc
          _ ≤ (|directionalDeriv (directions i) mu x| * (Cw*epsilon))*(‖phiHalf x‖*‖G x j‖) :=
            abs_scaled_clm_inner_le (K x) _ _ hKweak _ _
          _ ≤ ((Cmu*mu x)*(Cw*epsilon))*NN x := mul_le_mul
            (mul_le_mul_of_nonneg_right (hdmu x hx) (mul_nonneg hCw hepsilon))
            hproduct (by positivity) (by positivity)
          _ = _ := by ring
      have hd : |⟪mu x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| ≤
          (mu x*Cdw*epsilon)*NN x := by
        calc
          _ ≤ (|mu x| * (Cdw*epsilon))*(‖phiHalf x‖*‖G x j‖) :=
            abs_scaled_clm_inner_le _ (mu x) _ (hDKbound x hx) _ _
          _ = (mu x*Cdw*epsilon)*(‖phiHalf x‖*‖G x j‖) := by
            rw [abs_of_nonneg hmu0]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hproduct (by positivity)
      have hF : directionalDeriv (directions i) (fun y => mu y • W y) x =
          mu x • K x (G x i) + directionalDeriv (directions i) mu x • K x (phiHalf x) +
            mu x • (fderiv ℝ K x (directions i)) (phiHalf x) := by
        rw [directionalDeriv_smul (directions i) mu W hmu hW x]
        change directionalDeriv (directions i) mu x • K x (phiHalf x) +
          mu x • directionalDeriv (directions i) (fun y => K y (phiHalf y)) x = _
        rw [directionalDeriv_clm_apply (directions i) K phiHalf hK hphiHalf x,smul_add]
        dsimp [G]
        abel
      rw [hF,inner_add_left,inner_add_left]
      calc
        _ ≤ |⟪mu x • K x (G x i),G x j⟫_ℝ| +
            |⟪directionalDeriv (directions i) mu x • K x (phiHalf x),G x j⟫_ℝ| +
            |⟪mu x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| :=
          ActualPrincipalErrorCoefficient.abs_three_add_le _ _ _
        _ ≤ mu x*Cw*epsilon*NN x + (mu x*Cmu*Cw*epsilon)*NN x +
            (mu x*Cdw*epsilon)*NN x := add_le_add (add_le_add hp hm) hd
        _ = _ := by ring
    · have hnot : x ∉ tsupport phi := fun ht => hx (hsupport ht)
      have hnotHalf : x ∉ tsupport phiHalf := fun ht => hnot
        (tsupport_besselGraph_subset hO hD (1/2) phi phiHalf hhalf ht)
      have hz : phi x = 0 := image_eq_zero_of_notMem_tsupport hnot
      have h1 : phiOne x = 0 := spectralGraph_zero_input hO hD (besselWeight 1) _
        (by simpa only [sphereBesselGraph, hz] using hone x)
      have h3 : phiThree x = 0 := spectralGraph_zero_input hO hD (besselWeight (3/2)) _
        (by simpa only [sphereBesselGraph, hz] using hthree x)
      have hG (k : ι) : G x k = 0 :=
        directionalDeriv_eq_zero_of_notMem_tsupport (directions k) phiHalf x hnotHalf
      have hD (k : ι) : directionalDeriv (directions k) phi x = 0 :=
        directionalDeriv_eq_zero_of_notMem_tsupport (directions k) phi x hnot
      have hNN : NN x = 0 := by simp [NN,sourceNormSquareIntegrand,hD,hG,h1,h3]
      simp only [hG j,inner_zero_right,abs_zero,hNN,mul_zero,le_refl]
  have hint := norm_integral_le_of_norm_le
    (f := fun x => ⟪directionalDeriv (directions i) (fun y => mu y • W y) x,G x j⟫_ℝ)
    (hN.const_mul ((Cw+Cmu*Cw+Cdw)*epsilon))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,mu,NN,G] using hbound x))
  rw [integral_const_mul] at hint
  rw [hparts,abs_neg]
  simp_rw [hpair]
  rw [sourceNormSquare_eq_density_integral g hg L lam]
  simpa only [Real.norm_eq_abs,mu,NN,G] using hint

end OAI.AnisotropicCalderon.LocalizedPrincipalSecondForm
