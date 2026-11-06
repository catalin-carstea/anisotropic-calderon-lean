import Calderon.ActualHigherSMixedWordScalarUniformCaps

/-! Small actual scalar dictionary and pure word smoothness. Definitions below
are literal aliases of the original checked coefficient/frame/connection/radius
functions; original public statements are retained through the facade. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
open EnergyBridge ConnectionError ConformalDepth ReferenceWeightedApproximation
  ActualHigherSQuadraticZeroWords ActualNormalizedSecondMetricDrift SmoothMetricFrame MovingFrameConnection
  ActualHigherSLeadingBracketGain

def mixedWordPrincipalSlice (g g2 : MatrixField) (L q : ℝ) (i j : Fin 3) (x : R3) : ℝ :=
  referenceDensityPrincipalFrameCoefficient g g2 L q x i j

def mixedWordFrameSlice (g : MatrixField) (L q : ℝ) (i : Fin 3) (x : R3) : R3 :=
  referenceMetricGramFrame g L (q,x) i

def mixedWordConnectionSlice (g : MatrixField) (L q : ℝ) (i a b : Fin 3) (x : R3) : ℝ :=
  frameConnectionScalarJoint g L i a b (q,x)

lemma contDiff_mixedWordPrincipalSlice (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (q : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (mixedWordPrincipalSlice g g2 L q i j) := by
  have h := (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : R3 => (q,x)))
  unfold mixedWordPrincipalSlice
  simpa only [Function.comp_def] using h

lemma contDiff_mixedWordFrameSlice (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) : ContDiff ℝ ∞ (mixedWordFrameSlice g L q i) := by
  have h := (contDiff_referenceMetricGramFrame g hg L i).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : R3 => (q,x)))
  unfold mixedWordFrameSlice
  simpa only [Function.comp_def] using h

lemma contDiff_mixedWordConnectionSlice (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i a b : Fin 3) : ContDiff ℝ ∞ (mixedWordConnectionSlice g L q i a b) := by
  have h := (contDiff_frameConnectionScalarJoint g hg L i a b).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : R3 => (q,x)))
  unfold mixedWordConnectionSlice
  simpa only [Function.comp_def] using h

attribute [local irreducible] mixedWordPrincipalSlice mixedWordFrameSlice mixedWordConnectionSlice

def actualClearedWordCoefficient (g : MatrixField) (L : ℝ) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (z : ZeroWord) : R3 → ℝ :=
  clearedWordCoefficient (referenceRadius dr Ar p L)
    (mixedWordPrincipalSlice g g2 L q) (mixedWordFrameSlice g L q) (mixedWordConnectionSlice g L q) z

lemma contDiff_actualClearedWordCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (z : ZeroWord) :
    ContDiff ℝ ∞ (actualClearedWordCoefficient g L g2 dr Ar p q z) := by
  exact contDiff_clearedWordCoefficient (referenceRadius dr Ar p L)
    (mixedWordPrincipalSlice g g2 L q) (mixedWordFrameSlice g L q) (mixedWordConnectionSlice g L q)
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr)
    (contDiff_mixedWordPrincipalSlice g hg L g2 hg2 q)
    (contDiff_mixedWordFrameSlice g hg L q) (contDiff_mixedWordConnectionSlice g hg L q) z

lemma actualWordCoefficient_eq_actualClearedWordCoefficient (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (z : ZeroWord) :
    (fun x => actualWordCoefficient g L g2 dr Ar p q x z) =
      actualClearedWordCoefficient g L g2 dr Ar p q z := by
  unfold actualClearedWordCoefficient mixedWordPrincipalSlice mixedWordFrameSlice
    mixedWordConnectionSlice frameConnectionScalarJoint
  exact actualWordCoefficient_eq_cleared g hg L g2 dr Ar p hdr hAr q z

attribute [local irreducible] actualWordCoefficient actualClearedWordCoefficient

lemma contDiff_actualWordCoefficient_pure
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (z : ZeroWord) :
    ContDiff ℝ ∞ (fun x => actualWordCoefficient g L g2 dr Ar p q x z) := by
  rw [actualWordCoefficient_eq_actualClearedWordCoefficient g hg L g2 dr Ar p hdr hAr q z]
  exact contDiff_actualClearedWordCoefficient g hg L g2 hg2 dr Ar p hdr hAr q z

lemma contDiff_actualMixedWordScalar_pure
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (k i : Fin 3) (z : ZeroWord) :
    ContDiff ℝ ∞ (fun x => (referenceRadius dr Ar p L x)^2*
      firstCoordinateWeight g g2 L k i (ActualHigherSFormation.higherSParam L dr Ar p q x)*
        actualWordCoefficient g L g2 dr Ar p q x z) := by
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hW : ContDiff ℝ ∞ (fun x => firstCoordinateWeight g g2 L k i
      (ActualHigherSFormation.higherSParam L dr Ar p q x)) := by
    rw [ActualHigherSCoordinateWeightBounds.physical_firstCoordinateWeight_eq_base g g2 L dr Ar q p k i]
    exact (ActualHigherSCoordinateWeightBounds.contDiff_coordinateWeightBase g g2 hg hg2 L k i).comp
      (contDiff_const.prodMk contDiff_id)
  exact ((hR.pow 2).mul hW).mul
    (contDiff_actualWordCoefficient_pure g hg L g2 hg2 dr Ar p hdr hAr q z)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
