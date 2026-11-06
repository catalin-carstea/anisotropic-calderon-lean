import Calderon.FiniteHarmonicEnergy
import Calderon.SmoothSphereRotationProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CovariantHarmonicEnergy
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SmoothSphereRotationProjection FischerConnectionTransport MovingFrameConnection
  SmoothMetricFrame FrameCurvaturePolynomial FiniteHarmonicEnergy
  MetricFiberCovectorTransport MetricFiberMeasure MetricFiberFischer
  FiniteProfileNormComparison ConformalDepth RadiusProfile MetricOperator ReferenceDensityBounds
variable {ι : Type*} [Fintype ι]

/-- The actual probability-sphere realization of a finite coefficient family. -/
def finitePolynomialSphereMap (b : ι → MvPolynomial (Fin 3) ℝ) :
    (ι → ℝ) →L[ℝ] SphereL2 :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (polynomialSphereL2 (b j))

lemma finitePolynomialSphereMap_apply (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) :
    finitePolynomialSphereMap b (c x) = polynomialSphereL2 (finitePolynomialField b c x) := by
  simp [finitePolynomialSphereMap,finitePolynomialField,map_sum,map_smul]

lemma contDiff_polynomialSphereL2_finite (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun x => polynomialSphereL2 (finitePolynomialField b c x)) := by
  simpa only [Function.comp_def,finitePolynomialSphereMap_apply] using
    (finitePolynomialSphereMap b).contDiff.comp hc

lemma fderiv_polynomialSphereL2_finite (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (x X : R3) :
    fderiv ℝ (fun y => polynomialSphereL2 (finitePolynomialField b c y)) x X =
      polynomialSphereL2 (finitePolynomialFieldDerivative b c x X) := by
  have h := ((finitePolynomialSphereMap b).hasFDerivAt.comp x
    (hc.differentiable (by simp) x).hasFDerivAt).fderiv
  have heq : (fun y => finitePolynomialSphereMap b (c y)) =
      fun y => polynomialSphereL2 (finitePolynomialField b c y) := by
    funext y; exact finitePolynomialSphereMap_apply b c y
  change fderiv ℝ (fun y => finitePolynomialSphereMap b (c y)) x = _ at h
  rw [heq] at h
  rw [h,ContinuousLinearMap.comp_apply]
  simp [finitePolynomialSphereMap,finitePolynomialFieldDerivative,map_sum,map_smul]

/-- The true reference connection on the actual degree-k harmonic image. -/
def referenceHarmonicCovariantDerivative (g : MatrixField) (L lam : ℝ) (k : ℕ)
    (U : R3 → harmonicSphereSubspace k) (x X : R3) : harmonicSphereSubspace k :=
  fderiv ℝ U x X + (1/2:ℝ) •
    ∑ a : Fin 3, ∑ b : Fin 3,
      referenceFrameConnectionCoefficient g L lam x X a b •
        harmonicSphereRotation k a b (U x)

lemma polynomialSphereL2_finite_derivative_eq (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (U : R3 → harmonicSphereSubspace k) (hc : ContDiff ℝ ∞ c)
    (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (x X : R3) :
    polynomialSphereL2 (finitePolynomialFieldDerivative b c x X) =
      (fderiv ℝ U x X : SphereL2) := by
  have heq : (fun y => polynomialSphereL2 (finitePolynomialField b c y)) =
      fun y => (U y : SphereL2) := funext hrep
  rw [← fderiv_polynomialSphereL2_finite b c hc x X,heq]
  have h := ((harmonicSphereSubspace k).subtypeL.hasFDerivAt.comp x
    (hU.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun A : R3 →L[ℝ] SphereL2 => A X) h

lemma polynomialSphereL2_rotation_eq (k : ℕ) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (v : harmonicSphereSubspace k) (hrep : polynomialSphereL2 p = (v : SphereL2)) :
    polynomialSphereL2 (polynomialRotation i j p) =
      (harmonicSphereRotation k i j v : SphereL2) := by
  have hv : harmonicPolynomialSphereMap k ⟨p,hp⟩ = v := by
    apply Subtype.ext; exact hrep
  rw [← hv,harmonicSphereRotation_apply_image]
  rfl

theorem polynomialSphereL2_referenceCovariantDerivative (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace k)
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (x X : R3) :
    polynomialSphereL2 (referenceCovariantPolynomialDerivative g L lam b c x X) =
      (referenceHarmonicCovariantDerivative g L lam k U x X : SphereL2) := by
  rw [referenceCovariantPolynomialDerivative,map_add,
    polynomialSphereL2_finite_derivative_eq k b c U hc hU hrep x X,
    referenceFrameAngularPolynomial_eq_half_smul g hg L lam x X,map_smul]
  have hrot (a d : Fin 3) := polynomialSphereL2_rotation_eq k a d
    (finitePolynomialField b c x) (finitePolynomialField_harmonicHomogeneous k b hb c x)
    (U x) (hrep x)
  simp only [polynomialRotationCombination,map_sum,← smul_eq_C_mul,map_smul,hrot,
    referenceHarmonicCovariantDerivative,Submodule.coe_add,Submodule.coe_smul,
    Submodule.coe_sum]

lemma referenceFiberCovectorPair_self_norm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    referenceFiberCovectorPair g hg L lam x q q =
      ∑ i : Fin 3, ‖polynomialSphereL2 (q i)‖^2 := by
  simp only [referenceFiberCovectorPair,metricFrameCovectorPair_eq_sum,
    metricFramePolynomial_fiber_integral_pair,real_inner_self_eq_norm_sq]

/-- Exactly the manuscript's four-term single-mode energy in its genuine Gram frame. -/
def referenceHarmonicModeEnergyDensity (g : MatrixField) (lam δ R L : ℝ)
    (p k : ℕ) (U : R3 → harmonicSphereSubspace k) (x : R3) : ℝ :=
  let V := ‖U x‖^2
  let G := ∑ i : Fin 3, ‖referenceHarmonicCovariantDerivative g L lam k U x
    (referenceMetricGramFrame g L (lam,x) i)‖^2
  let beta := referenceProfileNorm g lam δ R p L x
  G+beta^2*(1+(k:ℝ))^2*V+beta⁻¹*(1+(k:ℝ))*G+beta*(1+(k:ℝ))^3*V

def referenceHarmonicModeEnergy (g : MatrixField) (lam δ R L : ℝ)
    (p k : ℕ) (U : R3 → harmonicSphereSubspace k) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*
    referenceHarmonicModeEnergyDensity g lam δ R L p k U x

theorem referenceHarmonicModeEnergyDensity_eq_polynomial (g : MatrixField)
    (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace k)
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (x : R3) :
    referenceHarmonicModeEnergyDensity g lam δ R L p k U x =
      referenceProfileModeEnergyDensity g hg lam δ R L p k b c x := by
  simp only [referenceHarmonicModeEnergyDensity,referenceProfileModeEnergyDensity,
    referenceFiberPolynomialSquare_norm,referenceFiberCovectorPair_self_norm,
    polynomialSphereL2_referenceCovariantDerivative g hg L lam k b hb c U hc hU hrep,
    hrep,Submodule.norm_coe]

theorem referenceHarmonicModeEnergy_eq_polynomial (g : MatrixField)
    (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace k)
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2)) :
    referenceHarmonicModeEnergy g lam δ R L p k U =
      referenceProfileModeEnergy g hg lam δ R L p k b c := by
  unfold referenceHarmonicModeEnergy referenceProfileModeEnergy
  simp_rw [referenceHarmonicModeEnergyDensity_eq_polynomial g hg lam δ R L p k b hb c U hc hU hrep]

theorem integrable_referenceHarmonicModeEnergy (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (U : R3 → harmonicSphereSubspace k)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2)) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      referenceHarmonicModeEnergyDensity g lam δ R L p k U x) := by
  simp_rw [referenceHarmonicModeEnergyDensity_eq_polynomial g hg lam δ R L p k b hb c U hc hU hrep]
  exact (referenceProfileModeEnergy_integrable_and_eq hF g hg lam δ R L p k
    hδ hR hL hp hk b hb c hc hcompact).1

end OAI.AnisotropicCalderon.CovariantHarmonicEnergy
