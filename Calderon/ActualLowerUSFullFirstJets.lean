import Calderon.ActualLowerUSFirstCoefficientJets
import Calderon.ActualLowerUSWeightedScalarJets
import Calderon.ActualLowerUSFiniteScalarJetSum
import Calderon.ActualLowerUSFirstScalarJets
import Calderon.ActualLowerUSFiniteNormBudget

/-!
Author: GPT-6.1 Sol. Before-code ../lower-r-z-full-d-first-jets-upfront.md.
Full actual D value and first coordinate jets; scalar sigma is derived inline.
No analytic cap callback, proof admission or author compilation.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts ActualReferenceDDHigherProfileJets
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondModelErrorAssembly
  ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth NormalizedPrincipalMetric
  ActualAngularHighDraft ActualAngularPiDraft ActualPhysicalMixedFirst ActualPhysicalMixedReferenceCancellation
  ActualScalarPrincipalAdjoint
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "LowMap" => Half →L[ℝ] Neg
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def fullFirstLowNormed : NormedAddCommGroup LowMap := inferInstance
attribute [local instance] fullFirstLowNormed
@[instance_reducible] private def fullFirstLowSpace : NormedSpace ℝ LowMap := inferInstance
attribute [local instance] fullFirstLowSpace
attribute [local irreducible] lowerAdjointFirstLow

/-- Exact original uniform full-D word-jet proposition. This definition has
identical quantifiers to the expanded target separately elaborated by Root. -/
def LowerAdjointFirstUniformWordBound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ) : Prop :=
    ∃ CD : ℝ, 0 < CD ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ j : Fin 3, HasCoordinateWordJetBound (E := LowMap) 1
        (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j) x
        (CD*referenceRadius dr Ar p L x) (actualReferenceBeta g L q dr Ar p x) 1

set_option diagnostics true in
/-- Full original D low coefficient jets, with the complete scalar product
estimated internally from actual compact background and radius jets. -/
theorem exists_lowerAdjointFirstLow_uniform_word_bound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    LowerAdjointFirstUniformWordBound hF hO hD g g2 hg hg2 L hL y0 rho := by
  obtain ⟨CS,hCS,hScalar⟩ := exists_nativeFirstScalarCoefficient_uniform_word_bound
    g g2 hg hg2 L hL y0 rho
  obtain ⟨CJ,hCJ,hAngular⟩ := exists_firstAngularCoefficient_uniform_word_bound
    g g2 hg hg2 L hL (closedBall y0 rho) (isCompact_closedBall _ _)
  let maps : Unit ⊕ FirstAngularIndex → LowMap := fun i => match i with
    | Sum.inl _ => JL
    | Sum.inr v => firstAngularLow hF hO hD v
  obtain ⟨N,hN,hm⟩ := exists_finite_family_norm_budget maps
  have hN0 : 0 ≤ N := hN.le
  let CR : ℝ := CS+CJ
  let CD : ℝ := (Fintype.card (Unit ⊕ FirstAngularIndex) : ℝ)*2*CR*N
  have hCR : 0 < CR := by dsimp only [CR]; positivity
  have hCD : 0 < CD := by dsimp only [CD]; positivity
  refine ⟨CD,hCD,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs j
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hSigma : HasCoordinateWordJetBound 1
      (nativeFirstScalarCoefficient g g2 L q dr Ar p j) x (CS*r) beta 0 :=
    hScalar q hq dr hdr hdr1 Ar hAr p hp x hx hb j
  have hsSmooth := contDiff_nativeFirstScalarCoefficient g g2 hg hg2 L q dr Ar p hdr hAr j
  have hNegSigma := hasCoordinateWordJetBound_neg 1
    (nativeFirstScalarCoefficient g g2 L q dr Ar p j) hsSmooth x (CS*r) beta 0 hSigma
  let coeff : Unit ⊕ FirstAngularIndex → R3 → ℝ := fun i => match i with
    | Sum.inl _ => fun y => -nativeFirstScalarCoefficient g g2 L q dr Ar p j y
    | Sum.inr v => fun y => firstAngularCoefficient g L g2 q dr Ar p j y v
  have hc (i : Unit ⊕ FirstAngularIndex) : ContDiff ℝ ∞ (coeff i) := by
    cases i with
    | inl z => exact hsSmooth.neg
    | inr v => exact contDiff_firstAngularCoefficient g g2 hg hg2 L q dr Ar p hdr hAr j v
  have hCoeff (i : Unit ⊕ FirstAngularIndex) :
      HasCoordinateWordJetBound 1 (coeff i) x (CR*r) beta 1 := by
    cases i with
    | inl z =>
      have hh := hasCoordinateWordJetBound_raise_degree 1
        (fun y => -nativeFirstScalarCoefficient g g2 L q dr Ar p j y)
        x (CS*r) beta 0 1 (by positivity) hb (by norm_num) hNegSigma
      exact hasCoordinateWordJetBound_mono 1 _ x (CS*r) (CR*r) beta 1 hh
        (by dsimp only [CR]; nlinarith [mul_nonneg hCJ.le hr.le]) hb0
    | inr v =>
      have hh := hAngular q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs j v
      exact hasCoordinateWordJetBound_mono 1 _ x (CJ*r) (CR*r) beta 1 hh
        (by dsimp only [CR]; nlinarith [mul_nonneg hCS.le hr.le]) hb0
  have hActual : lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j =
      (fun y => ∑ i : Unit ⊕ FirstAngularIndex, coeff i y • maps i) := by
    funext y
    simp only [lowerAdjointFirstLow,Fintype.sum_sum_type,Fintype.sum_unique,coeff,maps]
  have hGeneric := hasCoordinateWordJetBound_finite_scalar_sum
    (E := LowMap) 1 coeff hc maps x (CR*r) N beta 1 (by positivity) hN0 hb0 hm hCoeff
  have hBudget : (Fintype.card (Unit ⊕ FirstAngularIndex) : ℝ)*((2:ℝ)^1*(CR*r)*N) = CD*r := by
    dsimp only [CD]
    ring
  have hPC := congrArg (fun cap : ℝ => HasCoordinateWordJetBound (E := LowMap) 1
    (fun y => ∑ i : Unit ⊕ FirstAngularIndex, coeff i y • maps i) x cap beta 1) hBudget
  have hNew : HasCoordinateWordJetBound (E := LowMap) 1
      (fun y => ∑ i : Unit ⊕ FirstAngularIndex, coeff i y • maps i) x (CD*r) beta 1 :=
    Eq.mp hPC hGeneric
  have hPF := congrArg (fun f : R3 → LowMap => HasCoordinateWordJetBound (E := LowMap) 1
    f x (CD*r) beta 1) hActual
  exact Eq.mpr hPF hNew

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
