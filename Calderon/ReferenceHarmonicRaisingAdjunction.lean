import Calderon.ReferenceRaisingAdjunction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ReferenceHarmonicRaisingAdjunction
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SmoothSphereRotationProjection HarmonicDerivativeOperator CovariantHarmonicEnergy
  HarmonicRaisingModel ReferenceRaisingAdjunction MovingFrameConnection
  SmoothMetricFrame ReferenceDensityBounds FischerCovectorAdjunction

/-- Smoothness of the genuine connection on a variable smooth base direction. -/
lemma contDiff_referenceHarmonicCovariantDerivative (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (U : R3 → harmonicSphereSubspace k) (X : R3 → R3)
    (hU : ContDiff ℝ ∞ U) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun x => referenceHarmonicCovariantDerivative g L lam k U x (X x)) := by
  unfold referenceHarmonicCovariantDerivative
  apply ContDiff.add
  · exact (hU.fderiv_right (m := ∞) (by simp)).clm_apply hX
  · apply ContDiff.smul
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (1/2 : ℝ)))
    apply ContDiff.sum
    intro a _
    apply ContDiff.sum
    intro b _
    exact (contDiff_referenceFrameConnectionCoefficient_variable g hg L lam X hX a b).smul
      ((harmonicSphereRotation k a b).contDiff.comp hU)

lemma contDiff_referenceHarmonicWeightedExpression (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (U : R3 → harmonicSphereSubspace k) (X : R3 → R3) (f : R3 → ℝ) (w s : ℝ)
    (hU : ContDiff ℝ ∞ U) (hX : ContDiff ℝ ∞ X) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => s • referenceHarmonicCovariantDerivative g L lam k U x (X x) +
      (w * fderiv ℝ f x (X x)) • U x) := by
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => s)).smul
      (contDiff_referenceHarmonicCovariantDerivative g hg L lam k U X hU hX)).add
    (((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => w)).mul
      ((hf.fderiv_right (m := ∞) (by simp)).clm_apply hX)).smul hU)

lemma referenceHarmonicCovariantDerivative_eq_zero_of_notMem_tsupport
    (g : MatrixField) (L lam : ℝ) (k : ℕ) (U : R3 → harmonicSphereSubspace k)
    (x X : R3) (hx : x ∉ tsupport U) :
    referenceHarmonicCovariantDerivative g L lam k U x X = 0 := by
  simp only [referenceHarmonicCovariantDerivative,
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hx,image_eq_zero_of_notMem_tsupport hx,
    ContinuousLinearMap.zero_apply,map_zero,smul_zero,Finset.sum_const_zero,add_zero]

lemma referenceHarmonicWeightedExpression_eq_zero_of_notMem_tsupport
    (g : MatrixField) (L lam : ℝ) (k : ℕ) (U : R3 → harmonicSphereSubspace k)
    (f : R3 → ℝ) (w s : ℝ) (x X : R3) (hx : x ∉ tsupport U) :
    s • referenceHarmonicCovariantDerivative g L lam k U x X +
      (w * fderiv ℝ f x X) • U x = 0 := by
  rw [referenceHarmonicCovariantDerivative_eq_zero_of_notMem_tsupport g L lam k U x X hx,
    image_eq_zero_of_notMem_tsupport hx]
  simp

theorem contDiff_referenceHarmonicRaising (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (U : R3 → harmonicSphereSubspace (m+1)) (f : R3 → ℝ)
    (hU : ContDiff ℝ ∞ U) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (referenceHarmonicRaising hF g L lam m U f) := by
  unfold referenceHarmonicRaising
  apply ContDiff.sum
  intro i _
  apply (harmonicDerivativeAdjoint hF (m+1) i).contDiff.comp
  exact contDiff_referenceHarmonicWeightedExpression g hg L lam (m+1) U _ f ((m+1 : ℕ) : ℝ) 1
    hU (contDiff_referenceMetricGramFrame_slice g hg L lam i) hf

theorem contDiff_referenceHarmonicRaisingAdjoint (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (V : R3 → harmonicSphereSubspace ((m+1)+1)) (f : R3 → ℝ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (referenceHarmonicRaisingAdjoint hF g L lam m V f) := by
  unfold referenceHarmonicRaisingAdjoint
  apply ContDiff.sum
  intro i _
  apply (harmonicDerivative hF (m+1) i).contDiff.comp
  exact contDiff_referenceHarmonicWeightedExpression g hg L lam ((m+1)+1) V _ f
    ((m+1 : ℕ) : ℝ) (-1) hV (contDiff_referenceMetricGramFrame_slice g hg L lam i) hf

theorem hasCompactSupport_referenceHarmonicRaising (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (m : ℕ)
    (U : R3 → harmonicSphereSubspace (m+1)) (f : R3 → ℝ)
    (hcompact : HasCompactSupport U) :
    HasCompactSupport (referenceHarmonicRaising hF g L lam m U f) := by
  apply hcompact.mono'
  intro x hx
  by_contra hnot
  simp only [Function.mem_support] at hx
  apply hx
  unfold referenceHarmonicRaising referenceWeightedHarmonicDerivative
  simp only [referenceHarmonicWeightedExpression_eq_zero_of_notMem_tsupport
      g L lam (m+1) U f ((m+1 : ℕ) : ℝ) 1 x _ hnot,map_zero,Finset.sum_const_zero]

theorem hasCompactSupport_referenceHarmonicRaisingAdjoint (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (m : ℕ)
    (V : R3 → harmonicSphereSubspace ((m+1)+1)) (f : R3 → ℝ)
    (hcompact : HasCompactSupport V) :
    HasCompactSupport (referenceHarmonicRaisingAdjoint hF g L lam m V f) := by
  apply hcompact.mono'
  intro x hx
  by_contra hnot
  simp only [Function.mem_support] at hx
  apply hx
  unfold referenceHarmonicRaisingAdjoint referenceAdjointHarmonicInput
  simp only [referenceHarmonicWeightedExpression_eq_zero_of_notMem_tsupport
      g L lam ((m+1)+1) V f ((m+1 : ℕ) : ℝ) (-1) x _ hnot,map_zero,Finset.sum_const_zero]

lemma hasCompactSupport_real_inner_left {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U V : R3 → E) (hcompact : HasCompactSupport U) :
    HasCompactSupport (fun x => ⟪U x,V x⟫_ℝ) := by
  apply hcompact.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp [hx]

/-- The two full pairing integrands are ordinary integrable functions. -/
theorem integrable_referenceHarmonicRaising_pairings (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (U : R3 → harmonicSphereSubspace (m+1))
    (V : R3 → harmonicSphereSubspace ((m+1)+1)) (f : R3 → ℝ)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport U) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪referenceHarmonicRaising hF g L lam m U f x,V x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪U x,referenceHarmonicRaisingAdjoint hF g L lam m V f x⟫_ℝ) := by
  have hr : Continuous (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun x : R3 => x)))).continuous
  have hT := contDiff_referenceHarmonicRaising hF g hg L lam m U f hU hf
  have hA := contDiff_referenceHarmonicRaisingAdjoint hF g hg L lam m V f hV hf
  exact ⟨(hr.mul (hT.continuous.inner hV.continuous)).integrable_of_hasCompactSupport
      (hasCompactSupport_real_inner_left _ _
        (hasCompactSupport_referenceHarmonicRaising hF g L lam m U f hcompact)).mul_left,
    (hr.mul (hU.continuous.inner hA.continuous)).integrable_of_hasCompactSupport
      (hasCompactSupport_real_inner_left _ _ hcompact).mul_left⟩

/-- Genuine full reference-volume/probability-sphere formal adjunction on all
smooth compact actual harmonic fields in two adjacent positive degrees.
Finite representations are constructed in the proof, not hypotheses. -/
theorem compact_referenceHarmonicRaising_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (U : R3 → harmonicSphereSubspace (m+1))
    (V : R3 → harmonicSphereSubspace ((m+1)+1)) (f : R3 → ℝ)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hcompactU : HasCompactSupport U) (hcompactV : HasCompactSupport V) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceHarmonicRaising hF g L lam m U f x,V x⟫_ℝ) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪U x,referenceHarmonicRaisingAdjoint hF g L lam m V f x⟫_ℝ) := by
  have hUi : ContDiff ℝ ∞ (fun x => (U x : SphereL2)) :=
    (harmonicSphereSubspace (m+1)).subtypeL.contDiff.comp hU
  have hVi : ContDiff ℝ ∞ (fun x => (V x : SphereL2)) :=
    (harmonicSphereSubspace ((m+1)+1)).subtypeL.contDiff.comp hV
  obtain ⟨n,b,c,hb,hc,hcompactc,hrepc,_⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD (m+1)
      (fun x => (U x : SphereL2)) hUi (tsupport U) hcompactU
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; rfl)
  obtain ⟨n',d,z,hd,hz,hcompactz,hrepz,_⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD ((m+1)+1)
      (fun x => (V x : SphereL2)) hVi (tsupport V) hcompactV
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; rfl)
  have hrepU (x : R3) : polynomialSphereL2 (FischerConnectionTransport.finitePolynomialField b c x) =
      (U x : SphereL2) := by
    simpa only [sphereHarmonicCoordinate_subtype] using hrepc x
  have hrepV (x : R3) : polynomialSphereL2 (FischerConnectionTransport.finitePolynomialField d z x) =
      (V x : SphereL2) := by
    simpa only [sphereHarmonicCoordinate_subtype] using hrepz x
  have h := compact_reference_raising_polynomial_adjoint hF g hg L lam m b d hb hd c z f
    hc hz hf hcompactc
  simp_rw [polynomialSphereL2_referenceRaisedField hF g hg L lam m b hb c U hc hU hrepU,
    polynomialSphereL2_referenceAdjointField hF g hg L lam m d hd z V hz hV hrepV,
    hrepU,hrepV] at h
  exact h

end OAI.AnisotropicCalderon.ReferenceHarmonicRaisingAdjunction
