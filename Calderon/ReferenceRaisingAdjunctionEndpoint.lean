import Calderon.ReferenceHarmonicRaisingAdjunction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ReferenceRaisingAdjunctionEndpoint
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  HarmonicDerivativeOperator CovariantHarmonicEnergy HarmonicRaisingModel
  ReferenceRaisingAdjunction ReferenceHarmonicRaisingAdjunction
  FischerConnectionTransport ScalarContractedAdjunction PolynomialSlotCompatibility
  AllDegreeCovectorTransport MovingFrameConnection SmoothMetricFrame
  ReferenceDensityBounds AngularPolynomial

/-- Source T on the constant angular degree; B acts as zero. -/
def referenceHarmonicConstantRaising (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (U : R3 → harmonicSphereSubspace 0) (x : R3) : harmonicSphereSubspace 1 :=
  ∑ i : Fin 3, harmonicDerivativeAdjoint hF 0 i
    (referenceHarmonicCovariantDerivative g L lam 0 U x
      (referenceMetricGramFrame g L (lam,x) i))

/-- The independent full-adjoint expression on H1 takes values in H0. -/
def referenceHarmonicDegreeOneRaisingAdjoint (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (V : R3 → harmonicSphereSubspace 1) (x : R3) : harmonicSphereSubspace 0 :=
  ∑ i : Fin 3, harmonicDerivative hF 0 i
    (-referenceHarmonicCovariantDerivative g L lam 1 V x
      (referenceMetricGramFrame g L (lam,x) i))

def referenceHarmonicDegreeOneRaisingDefect (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (V : R3 → harmonicSphereSubspace 1) (f : R3 → ℝ) (x : R3) :
    harmonicSphereSubspace 0 :=
  ∑ i : Fin 3, fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i) •
    harmonicDerivative hF 0 i (V x)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Intermediate representations are discharged in the actual-field theorem below. -/
theorem compact_referenceHarmonicConstantRaising_adjoint_of_representation
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j, b j ∈ harmonicHomogeneous 0) (hd : ∀ j, d j ∈ harmonicHomogeneous 1)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (U : R3 → harmonicSphereSubspace 0) (V : R3 → harmonicSphereSubspace 1)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport c)
    (hrepU : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (hrepV : ∀ x, polynomialSphereL2 (finitePolynomialField d z x) = (V x : SphereL2)) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceHarmonicConstantRaising hF g L lam U x,V x⟫_ℝ) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪U x,referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V x⟫_ℝ) := by
  let e := fun x => referenceMetricGramFrame g L (lam,x)
  have hleft (x : R3) :
      ⟪referenceHarmonicConstantRaising hF g L lam U x,V x⟫_ℝ =
      ∑ i : Fin 3, fischerInner
        (referenceCovariantPolynomialDerivative g L lam b c x (e x i))
        (finitePolynomialField (fun j => pderiv i (d j)) z x) := by
    unfold referenceHarmonicConstantRaising
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_harmonicDerivativeAdjoint]
    change ⟪(referenceHarmonicCovariantDerivative g L lam 0 U x (e x i) : SphereL2),
      (harmonicDerivative hF 0 i (V x) : SphereL2)⟫_ℝ = _
    rw [← polynomialSphereL2_referenceCovariantDerivative g hg L lam 0 b hb c U hc hU hrepU,
      ← polynomialSphereL2_harmonicDerivative hF 0 i _
        (finitePolynomialField_harmonicHomogeneous 1 d hd z x) (V x) (hrepV x)]
    rw [hF 0 _ _
      (referenceCovariantPolynomialDerivative_harmonicHomogeneous_all g hg L lam 0 b hb c x _)
      (pderiv_harmonicHomogeneous_succ 0 i _
        (finitePolynomialField_harmonicHomogeneous 1 d hd z x))]
    simp only [normalizedFischerInner,sphereNormalization_zero,div_one,finitePolynomialField_partial]
  have hright (x : R3) :
      ⟪U x,referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V x⟫_ℝ =
      -(∑ i : Fin 3, fischerInner (finitePolynomialField b c x)
        (pderiv i (referenceCovariantPolynomialDerivative g L lam d z x (e x i)))) := by
    unfold referenceHarmonicDegreeOneRaisingAdjoint
    rw [inner_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_neg,inner_neg_right]
    change -⟪(U x : SphereL2),(harmonicDerivative hF 0 i
      (referenceHarmonicCovariantDerivative g L lam 1 V x (e x i)) : SphereL2)⟫_ℝ = _
    rw [← hrepU x,← polynomialSphereL2_harmonicDerivative hF 0 i _
      (referenceCovariantPolynomialDerivative_harmonicHomogeneous_all g hg L lam 1 d hd z x _)
      _ (polynomialSphereL2_referenceCovariantDerivative g hg L lam 1 d hd z V hz hV hrepV x _)]
    rw [hF 0 _ _ (finitePolynomialField_harmonicHomogeneous 0 b hb c x)
      (pderiv_harmonicHomogeneous_succ 0 i _
        (referenceCovariantPolynomialDerivative_harmonicHomogeneous_all g hg L lam 1 d hd z x _))]
    simp only [normalizedFischerInner,sphereNormalization_zero,div_one]
  have hbase := compact_reference_contracted_covector_fischer_adjoint g hg L lam
    b (fun j i => pderiv i (d j)) c z hc hz hcompact
  simp_rw [referenceCovectorPolynomialDerivative_partial] at hbase
  simp_rw [hleft,hright,mul_neg]
  rw [integral_neg]
  exact hbase

theorem contDiff_referenceHarmonicConstantRaising (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → harmonicSphereSubspace 0) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (referenceHarmonicConstantRaising hF g L lam U) := by
  unfold referenceHarmonicConstantRaising
  apply ContDiff.sum
  intro i _
  exact (harmonicDerivativeAdjoint hF 0 i).contDiff.comp
    (contDiff_referenceHarmonicCovariantDerivative g hg L lam 0 U _ hU
      (contDiff_referenceMetricGramFrame_slice g hg L lam i))

theorem contDiff_referenceHarmonicDegreeOneRaisingAdjoint (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (V : R3 → harmonicSphereSubspace 1) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V) := by
  unfold referenceHarmonicDegreeOneRaisingAdjoint
  apply ContDiff.sum
  intro i _
  exact (harmonicDerivative hF 0 i).contDiff.comp
    (contDiff_referenceHarmonicCovariantDerivative g hg L lam 1 V _ hV
      (contDiff_referenceMetricGramFrame_slice g hg L lam i)).neg

theorem hasCompactSupport_referenceHarmonicConstantRaising (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (U : R3 → harmonicSphereSubspace 0)
    (hcompact : HasCompactSupport U) :
    HasCompactSupport (referenceHarmonicConstantRaising hF g L lam U) := by
  apply hcompact.mono'
  intro x hx
  by_contra hnot
  simp only [Function.mem_support] at hx
  apply hx
  unfold referenceHarmonicConstantRaising
  simp only [referenceHarmonicCovariantDerivative_eq_zero_of_notMem_tsupport
    g L lam 0 U x _ hnot,map_zero,Finset.sum_const_zero]

theorem hasCompactSupport_referenceHarmonicDegreeOneRaisingAdjoint (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (V : R3 → harmonicSphereSubspace 1)
    (hcompact : HasCompactSupport V) :
    HasCompactSupport (referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V) := by
  apply hcompact.mono'
  intro x hx
  by_contra hnot
  simp only [Function.mem_support] at hx
  apply hx
  unfold referenceHarmonicDegreeOneRaisingAdjoint
  simp only [referenceHarmonicCovariantDerivative_eq_zero_of_notMem_tsupport
    g L lam 1 V x _ hnot,neg_zero,map_zero,Finset.sum_const_zero]

theorem integrable_referenceHarmonicConstantRaising_pairings (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → harmonicSphereSubspace 0) (V : R3 → harmonicSphereSubspace 1)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport U) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪referenceHarmonicConstantRaising hF g L lam U x,V x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪U x,referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V x⟫_ℝ) := by
  have hr : Continuous (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).prodMk
        (contDiff_id : ContDiff ℝ ∞ (fun x : R3 => x)))).continuous
  have hT := contDiff_referenceHarmonicConstantRaising hF g hg L lam U hU
  have hA := contDiff_referenceHarmonicDegreeOneRaisingAdjoint hF g hg L lam V hV
  exact ⟨(hr.mul (hT.continuous.inner hV.continuous)).integrable_of_hasCompactSupport
      (hasCompactSupport_real_inner_left _ _
        (hasCompactSupport_referenceHarmonicConstantRaising hF g L lam U hcompact)).mul_left,
    (hr.mul (hU.continuous.inner hA.continuous)).integrable_of_hasCompactSupport
      (hasCompactSupport_real_inner_left _ _ hcompact).mul_left⟩

/-- Full reference-volume endpoint adjunction, with no representation hypotheses. -/
theorem compact_referenceHarmonicConstantRaising_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → harmonicSphereSubspace 0) (V : R3 → harmonicSphereSubspace 1)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hcompactU : HasCompactSupport U) (hcompactV : HasCompactSupport V) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceHarmonicConstantRaising hF g L lam U x,V x⟫_ℝ) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪U x,referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V x⟫_ℝ) := by
  have hUi : ContDiff ℝ ∞ (fun x => (U x : SphereL2)) :=
    (harmonicSphereSubspace 0).subtypeL.contDiff.comp hU
  have hVi : ContDiff ℝ ∞ (fun x => (V x : SphereL2)) :=
    (harmonicSphereSubspace 1).subtypeL.contDiff.comp hV
  obtain ⟨n,b,c,hb,hc,hcompactc,hrepc,_⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD 0
      (fun x => (U x : SphereL2)) hUi (tsupport U) hcompactU
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; rfl)
  obtain ⟨n',d,z,hd,hz,hcompactz,hrepz,_⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD 1
      (fun x => (V x : SphereL2)) hVi (tsupport V) hcompactV
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; rfl)
  apply compact_referenceHarmonicConstantRaising_adjoint_of_representation hF g hg L lam
    b d hb hd c z U V hc hz hU hV hcompactc
  · intro x
    simpa only [sphereHarmonicCoordinate_subtype] using hrepc x
  · intro x
    simpa only [sphereHarmonicCoordinate_subtype] using hrepz x

/-- The source defect on H1 includes its constant output. -/
theorem referenceHarmonicLowering_zero_sub_adjoint (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (V : R3 → harmonicSphereSubspace 1)
    (f : R3 → ℝ) (x : R3) :
    referenceHarmonicLowering hF g L lam 0 V f x -
      referenceHarmonicDegreeOneRaisingAdjoint hF g L lam V x =
      referenceHarmonicDegreeOneRaisingDefect hF g L lam V f x := by
  unfold referenceHarmonicLowering referenceHarmonicDegreeOneRaisingAdjoint
    referenceHarmonicDegreeOneRaisingDefect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [referenceWeightedHarmonicDerivative,Nat.zero_add,Nat.cast_one,
    map_add,map_smul,map_neg]
  module

end OAI.AnisotropicCalderon.ReferenceRaisingAdjunctionEndpoint
