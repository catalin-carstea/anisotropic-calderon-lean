import Calderon.HarmonicDerivativeOperator

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.HarmonicRaisingModel
open SphereHarmonic SmoothSphereRotationProjection HarmonicDerivativeOperator
  CovariantHarmonicEnergy FischerConnectionTransport WeightedFischerSquare
  FiniteRaisingEnergy SmoothMetricFrame ReferenceDensityBounds SphereDerivativeAdjoint
  SphereHilbertDecomposition AngularPolynomial
variable {ι : Type*} [Fintype ι]

lemma sphereRaising_eq_sum_sphereDerivativeAdjoint (m : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    sphereRaising m q = ∑ i : Fin 3, sphereDerivativeAdjoint (m+1) i (q i) := by
  simp_rw [sphereDerivativeAdjoint_eq_raisingComponent (m+1) (by omega)]
  simp only [raisingComponent,Nat.add_sub_cancel]
  rw [← sphereRaising_sum_family]
  congr 1
  funext j
  simp [Pi.single_apply]

def referenceWeightedHarmonicDerivative (g : MatrixField) (L lam : ℝ) (k : ℕ)
    (U : R3 → harmonicSphereSubspace k) (f : R3 → ℝ) (s : ℝ) (x X : R3) :
    harmonicSphereSubspace k :=
  s • referenceHarmonicCovariantDerivative g L lam k U x X +
    ((k:ℝ)*fderiv ℝ f x X) • U x

lemma polynomialSphereL2_referenceWeightedDerivative (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace k)
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) (s : ℝ) (x X : R3) :
    polynomialSphereL2 (referenceWeightedPolynomialDerivative g L lam b c f k s x X) =
      (referenceWeightedHarmonicDerivative g L lam k U f s x X : SphereL2) := by
  simp only [referenceWeightedPolynomialDerivative,referenceWeightedHarmonicDerivative,
    ← smul_eq_C_mul,map_add,map_smul,
    polynomialSphereL2_referenceCovariantDerivative g hg L lam k b hb c U hc hU hrep,
    hrep,Submodule.coe_add,Submodule.coe_smul]

/-- The source T restricted to one genuine positive harmonic input. -/
def referenceHarmonicRaising (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (m : ℕ) (U : R3 → harmonicSphereSubspace (m+1))
    (f : R3 → ℝ) (x : R3) : harmonicSphereSubspace ((m+1)+1) :=
  ∑ i : Fin 3, harmonicDerivativeAdjoint hF (m+1) i
    (referenceWeightedHarmonicDerivative g L lam (m+1) U f 1 x
      (referenceMetricGramFrame g L (lam,x) i))

/-- The source Tflat; its full base adjoint identification is a separate obligation. -/
def referenceHarmonicLowering (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (m : ℕ) (U : R3 → harmonicSphereSubspace (m+1))
    (f : R3 → ℝ) (x : R3) : harmonicSphereSubspace m :=
  ∑ i : Fin 3, harmonicDerivative hF m i
    (referenceWeightedHarmonicDerivative g L lam (m+1) U f (-1) x
      (referenceMetricGramFrame g L (lam,x) i))

theorem polynomialSphereL2_referenceRaisedField (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace (m+1))
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) (x : R3) :
    polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x) =
      (referenceHarmonicRaising hF g L lam m U f x : SphereL2) := by
  let q := referenceWeightedFramePolynomialField g L lam b c f (m+1) 1 x
  have hq (i : Fin 3) : q i ∈ harmonicHomogeneous (m+1) :=
    referenceWeightedFramePolynomialField_harmonicHomogeneous g hg L lam m b hb c f 1 x i
  have himage (i : Fin 3) : harmonicPolynomialSphereMap (m+1) ⟨q i,hq i⟩ =
      referenceWeightedHarmonicDerivative g L lam (m+1) U f 1 x
        (referenceMetricGramFrame g L (lam,x) i) := by
    apply Subtype.ext
    change polynomialSphereL2 (q i) =
      (referenceWeightedHarmonicDerivative g L lam (m+1) U f 1 x
        (referenceMetricGramFrame g L (lam,x) i) : SphereL2)
    simpa only [q,referenceWeightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      polynomialSphereL2_referenceWeightedDerivative g hg L lam (m+1) b hb c U hc hU hrep f 1 x
        (referenceMetricGramFrame g L (lam,x) i)
  change polynomialSphereL2 (sphereRaising m q) = _
  rw [sphereRaising_eq_sum_sphereDerivativeAdjoint,map_sum]
  unfold referenceHarmonicRaising
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← himage i,harmonicDerivativeAdjoint_apply_image]
  rfl

theorem polynomialSphereL2_referenceLoweredField (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace (m+1))
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) (x : R3) :
    polynomialSphereL2 (referenceLoweredPolynomialField g L lam b c f m x) =
      (referenceHarmonicLowering hF g L lam m U f x : SphereL2) := by
  let q := referenceWeightedFramePolynomialField g L lam b c f (m+1) (-1) x
  have hq (i : Fin 3) : q i ∈ harmonicHomogeneous (m+1) :=
    referenceWeightedFramePolynomialField_harmonicHomogeneous g hg L lam m b hb c f (-1) x i
  have himage (i : Fin 3) : harmonicPolynomialSphereMap (m+1) ⟨q i,hq i⟩ =
      referenceWeightedHarmonicDerivative g L lam (m+1) U f (-1) x
        (referenceMetricGramFrame g L (lam,x) i) := by
    apply Subtype.ext
    change polynomialSphereL2 (q i) =
      (referenceWeightedHarmonicDerivative g L lam (m+1) U f (-1) x
        (referenceMetricGramFrame g L (lam,x) i) : SphereL2)
    simpa only [q,referenceWeightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      polynomialSphereL2_referenceWeightedDerivative g hg L lam (m+1) b hb c U hc hU hrep f (-1) x
        (referenceMetricGramFrame g L (lam,x) i)
  change polynomialSphereL2 (∑ i : Fin 3, pderiv i (q i)) = _
  rw [map_sum]
  unfold referenceHarmonicLowering
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← himage i,harmonicDerivative_apply_image]
  rfl

def referenceHarmonicRaisingEnergy (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (m : ℕ) (U : R3 → harmonicSphereSubspace (m+1)) (f : R3 → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*‖referenceHarmonicRaising hF g L lam m U f x‖^2

def referenceHarmonicLoweringEnergy (hF : SphereFischerInner) (g : MatrixField)
    (L lam : ℝ) (m : ℕ) (U : R3 → harmonicSphereSubspace (m+1)) (f : R3 → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*‖referenceHarmonicLowering hF g L lam m U f x‖^2

theorem referenceHarmonicRaisingEnergy_eq_polynomial (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace (m+1))
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) :
    referenceHarmonicRaisingEnergy hF g L lam m U f = referenceRaisingEnergy g L lam b c f m := by
  unfold referenceHarmonicRaisingEnergy referenceRaisingEnergy
  simp_rw [polynomialSphereL2_referenceRaisedField hF g hg L lam m b hb c U hc hU hrep,Submodule.norm_coe]

theorem referenceHarmonicLoweringEnergy_eq_polynomial (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace (m+1))
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) :
    referenceHarmonicLoweringEnergy hF g L lam m U f = referenceLoweringEnergy g L lam b c f m := by
  unfold referenceHarmonicLoweringEnergy referenceLoweringEnergy
  simp_rw [polynomialSphereL2_referenceLoweredField hF g hg L lam m b hb c U hc hU hrep,Submodule.norm_coe]

theorem integrable_referenceHarmonicRaising (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace (m+1))
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      ‖referenceHarmonicRaising hF g L lam m U f x‖^2) := by
  have h := integrable_referenceRaisingEnergy hF g hg L lam m b hb c f hc hf hcompact
  simpa only [polynomialSphereL2_referenceRaisedField hF g hg L lam m b hb c U hc hU hrep,
    Submodule.norm_coe] using h

theorem integrable_referenceHarmonicLowering (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace (m+1))
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      ‖referenceHarmonicLowering hF g L lam m U f x‖^2) := by
  have h := integrable_referenceLoweringEnergy hF g hg L lam m b hb c f hc hf hcompact
  simpa only [polynomialSphereL2_referenceLoweredField hF g hg L lam m b hb c U hc hU hrep,
    Submodule.norm_coe] using h

end OAI.AnisotropicCalderon.HarmonicRaisingModel
