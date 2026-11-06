import Calderon.ActualHigherSZeroCoefficientJetBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
open ReferenceDensityBounds ActualHigherSZeroCoefficientJetBounds
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)

/-- Fixed coordinate covector, in the original Euclidean R3 structure. -/
def coordinateCovector (k : Fin 3) : R3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) k

def hessianTangent (k : Fin 3) : Tpar := ((0,(0,0)),coordinateCovector k)

def basicTangent (t : Tpar) (X : R3) : Tpar := ((0,(X,t.2 X)),0)

lemma vector_eq_coordinate_sum (v : R3) : v = ∑ k : Fin 3, v k • coordinateDirection k := by
  ext i
  fin_cases i <;> simp [coordinateDirection,Fin.sum_univ_three,Pi.single_apply]

lemma covector_eq_coordinate_sum (ell : R3 →L[ℝ] ℝ) :
    ell = ∑ k : Fin 3, ell (coordinateDirection k) • coordinateCovector k := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg ell (vector_eq_coordinate_sum v)
  simpa only [map_sum,map_smul,smul_eq_mul,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,coordinateCovector,EuclideanSpace.coe_proj,mul_comm] using h

lemma hessian_apply_eq_coordinate_sum (D : R3 →L[ℝ] R3 →L[ℝ] ℝ) (X : R3) :
    D X = ∑ mk : Fin 3 × Fin 3, (hessianEntry mk D*X mk.1) • coordinateCovector mk.2 := by
  have h := congrArg D (vector_eq_coordinate_sum X)
  calc
    D X = ∑ m : Fin 3, X m • D (coordinateDirection m) := by
      simpa only [map_sum,map_smul] using h
    _ = ∑ m : Fin 3, X m • (∑ k : Fin 3, D (coordinateDirection m) (coordinateDirection k) • coordinateCovector k) := by
      apply Finset.sum_congr rfl
      intro m _
      exact congrArg (fun z : R3 →L[ℝ] ℝ => X m • z) (covector_eq_coordinate_sum (D (coordinateDirection m)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.smul_sum,smul_smul]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      change (X m*D (coordinateDirection m) (coordinateDirection k)) • coordinateCovector k =
        (D (coordinateDirection m) (coordinateDirection k)*X m) • coordinateCovector k
      rw [mul_comm]

lemma parameterTangent_split (t : Tpar) (D : R3 →L[ℝ] R3 →L[ℝ] ℝ) (X : R3) :
    ((0,(X,t.2 X)),D X) = basicTangent t X+
      ∑ mk : Fin 3 × Fin 3, hessianEntry mk D • (X mk.1 • hessianTangent mk.2) := by
  rw [hessian_apply_eq_coordinate_sum D X]
  apply Prod.ext
  · simp [basicTangent,hessianTangent,Fintype.sum_prod_type,Fin.sum_univ_three]
  · simp [basicTangent,hessianTangent,smul_smul,Fintype.sum_prod_type,Fin.sum_univ_three]

lemma fderiv_radiusParameter_apply (RR : R3 → ℝ) (hR : ContDiff ℝ ∞ RR)
    (q : ℝ) (x X : R3) :
    fderiv ℝ (fun y => ((q,(y,RR y)),fderiv ℝ RR y)) x X =
      ((0,(X,fderiv ℝ RR x X)),fderiv ℝ (fderiv ℝ RR) x X) := by
  have hRR := (hR.differentiable (by simp) x).hasFDerivAt
  have hdR := ((hR.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hId := hasFDerivAt_id (𝕜 := ℝ) x
  have hc := hasFDerivAt_const (𝕜 := ℝ) q x
  have hh := (hc.prodMk (hId.prodMk hRR)).prodMk hdR
  exact congrArg (fun A => A X) hh.fderiv

section Chain
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact chain-rule decomposition, valid at a genuinely differentiable parameter point. -/
lemma fderiv_radiusComposite_split (RR : R3 → ℝ) (hR : ContDiff ℝ ∞ RR)
    (f : Tpar → V) (q : ℝ) (x X : R3)
    (hf : DifferentiableAt ℝ f ((q,(x,RR x)),fderiv ℝ RR x)) :
    fderiv ℝ (fun y => f ((q,(y,RR y)),fderiv ℝ RR y)) x X =
      fderiv ℝ f ((q,(x,RR x)),fderiv ℝ RR x)
        (basicTangent ((q,(x,RR x)),fderiv ℝ RR x) X)+
      ∑ mk : Fin 3 × Fin 3, hessianEntry mk (fderiv ℝ (fderiv ℝ RR) x) •
        (X mk.1 • fderiv ℝ f ((q,(x,RR x)),fderiv ℝ RR x) (hessianTangent mk.2)) := by
  have hTP : ContDiff ℝ ∞ (fun y => ((q,(y,RR y)),fderiv ℝ RR y)) :=
    (contDiff_const.prodMk (contDiff_id.prodMk hR)).prodMk
      (hR.fderiv_right (m := ∞) (by simp))
  have hc := fderiv_comp x hf (hTP.differentiable (by simp) x)
  have he : (fun y => f ((q,(y,RR y)),fderiv ℝ RR y)) =
      f ∘ (fun y => ((q,(y,RR y)),fderiv ℝ RR y)) := rfl
  rw [he,hc,ContinuousLinearMap.comp_apply,fderiv_radiusParameter_apply RR hR q x X,
    parameterTangent_split ((q,(x,RR x)),fderiv ℝ RR x) (fderiv ℝ (fderiv ℝ RR) x) X]
  simp only [map_add,map_sum,map_smul]
end Chain

section ModuleAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Radius clearing for one complete second row, before contracting with Q. -/
lemma clear_second_row {κ : Type*} [Fintype κ] (r fi fj li lj : ℝ)
    (DB O1 O2 L1 L2 J G : V) (c : κ → ℝ) (D : κ → V)
    (hi : r*fi = li) (hj : r*fj = lj) :
    r^2 • ((DB+∑ k, c k • D k)+O1+fi•L1+O2+fj•L2+fi•J-G) =
      r • (r•(DB+O1+O2-G)+(li•L1+lj•L2+li•J))+
        ∑ k, (r^2*c k) • D k := by
  have hi2 : r^2*fi = r*li := by calc
    _ = r*(r*fi) := by ring
    _ = _ := by rw [hi]
  have hj2 : r^2*fj = r*lj := by calc
    _ = r*(r*fj) := by ring
    _ = _ := by rw [hj]
  simp only [smul_add,smul_sub,Finset.smul_sum,smul_smul,hi2,hj2]
  module

/-- Finite contraction of the actual row factorisation, with both original Q orders kept. -/
lemma sum_factored_rows {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (Z A B : ι → V) (h : κ → ℝ) (D : ι → κ → V)
    (hz : ∀ i, r^2 • Z i = r • (r•A i+B i)+∑ k, (r^2*h k) • D i k) :
    r^2 • (∑ i, Z i) = r • (r•(∑ i, A i)+∑ i, B i)+
      ∑ k, (r^2*h k) • (∑ i, D i k) := by
  calc
    _ = ∑ i, r^2 • Z i := by rw [Finset.smul_sum]
    _ = ∑ i, (r • (r•A i+B i)+∑ k, (r^2*h k) • D i k) :=
      Finset.sum_congr rfl (fun i _ => hz i)
    _ = (∑ i, r • (r•A i+B i)) + ∑ i, ∑ k, (r^2*h k) • D i k :=
      Finset.sum_add_distrib
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [←Finset.smul_sum,Finset.sum_add_distrib]

/-- Remainder of the literal zero coefficient after the second-row contraction. -/
lemma assemble_zero_factors (r : ℝ) (A B D H Q S Z : V)
    (hz : r^2 • Z = r • (r•A+B)+H) :
    (r^2•Z+r^2•D)+r•Q+r^3•S =
      r•(r•A+B+r•D+Q+r^2•S)+H := by
  rw [hz]
  module
end ModuleAlgebra

open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ConformalDepth ReferenceWeightedApproximation ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualGeneratorRadialGainedRows ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms SphereHarmonic.DegreeGraphLifting ActualHorizontalNormBridge NormalCoordinatesFrame
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def factorHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighNormed
@[instance_reducible] private def factorHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighSpace
@[instance_reducible] private def factorLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowNormed
@[instance_reducible] private def factorLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowSpace
@[instance_reducible] private def factorZeroNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroNormed
@[instance_reducible] private def factorZeroSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroSpace
@[instance_reducible] private def factorParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] factorParameterNormed
@[instance_reducible] private def factorParameterSpace : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] factorParameterSpace
@[instance_reducible] private def factorDerivativeNormed : NormedAddCommGroup (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeNormed
@[instance_reducible] private def factorDerivativeSpace : NormedSpace ℝ (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeSpace

def parameterGramFrame (g : MatrixField) (L : ℝ) (i : Fin 3) (t : Tpar) : R3 :=
  referenceMetricGramFrame g L (t.1.1,t.1.2.1) i

def parameterConnection (g : MatrixField) (L : ℝ) (i k j : Fin 3) (t : Tpar) : ℝ :=
  referenceFrameConnectionJoint g L (fun z => referenceMetricGramFrame g L z i)
    (t.1.1,t.1.2.1) k j

lemma parameterConnection_eq (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (i k j : Fin 3) (t : Tpar) : parameterConnection g L i k j t =
    referenceFrameConnectionCoefficient g L t.1.1 t.1.2.1 (parameterGramFrame g L i t) k j :=
  referenceFrameConnectionJoint_eq g hg L _ _ k j

lemma contDiff_parameterGramFrame (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (parameterGramFrame g L i) :=
  (contDiff_referenceMetricGramFrame g hg L i).comp
    ((contDiff_fst.fst).prodMk (contDiff_fst.snd.fst))

lemma contDiff_parameterConnection (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i k j : Fin 3) :
    ContDiff ℝ ∞ (parameterConnection g L i k j) :=
  (contDiff_referenceFrameConnectionJoint g hg L _ (contDiff_referenceMetricGramFrame g hg L i) k j).comp
    ((contDiff_fst.fst).prodMk (contDiff_fst.snd.fst))

def parameterLowerAngular (g : MatrixField) (L : ℝ) (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, parameterConnection g L i a b t • sphereSobolevRotationL (1/2 : ℝ) a b

def parameterHighAngular (g : MatrixField) (L : ℝ) (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, parameterConnection g L i a b t • sphereSobolevRotationL (3/2 : ℝ) a b

lemma parameterLowerAngular_eq (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) (t : Tpar) :
    parameterLowerAngular g L i t = referenceLowerHorizontalAngularL g L t.1.1 t.1.2.1 i := by
  simp only [parameterLowerAngular,referenceLowerHorizontalAngularL,parameterConnection_eq g hg L,
    parameterGramFrame]

lemma parameterHighAngular_eq (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) (t : Tpar) :
    parameterHighAngular g L i t = referenceHighHorizontalAngularL g L t.1.1 t.1.2.1 i := by
  simp only [parameterHighAngular,referenceHighHorizontalAngularL,parameterConnection_eq g hg L,
    parameterGramFrame]

lemma contDiff_parameterLowerAngular (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (parameterLowerAngular g L i) := by
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact (contDiff_parameterConnection g hg L i a b).smul contDiff_const

lemma contDiff_parameterHighAngular (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (parameterHighAngular g L i) := by
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact (contDiff_parameterConnection g hg L i a b).smul contDiff_const

lemma contDiff_basicTangent_gram (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun t => basicTangent t (parameterGramFrame g L i t)) :=
  (contDiff_const.prodMk ((contDiff_parameterGramFrame g hg L i).prodMk
    (contDiff_snd.clm_apply (contDiff_parameterGramFrame g hg L i)))).prodMk contDiff_const

attribute [local irreducible] canonicalHigh canonicalLow referenceDensityPrincipalFrameCoefficient
 normalizedSecondDriftFrameJoint referenceMetricGramFrame

section Native
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "XP" => parameterGramFrame g L
local notation "GP" => parameterConnection g L
local notation "OL" => parameterLowerAngular g L
local notation "OH" => parameterHighAngular g L
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QP" g2:max i:max j:max t:max => referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i j
local notation "DP" g2:max i:max t:max => normalizedSecondDriftFrameJoint g g2 L i (t.1.1,t.1.2.1)

def regularZeroRow (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Neg :=
  (JL).comp (fderiv ℝ (EH j) t (basicTangent t (XP i t)))+
    (OL i t).comp (EH j t)+(EL i t).comp (OH j t)-
    ∑ k : Fin 3, GP i k j t • (JL).comp (EH k t)
local notation "ZR" => regularZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def logarithmicZeroRow (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Neg :=
  (t.2 (XP i t)) • (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp (EH j t)+
    (t.2 (XP j t)) • (EL i t).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ))+
    (t.2 (XP i t)) • (JL).comp (EH j t)
local notation "ZL" => logarithmicZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- All non-Hessian factors; no inverse radius or logarithm at r=0. -/
def zeroParameterFactor (g2 : MatrixField) (t : Tpar) : Hi →L[ℝ] Neg :=
  t.1.2.2 • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • ZR i j t)+
    (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • ZL i j t)+
    t.1.2.2 • (∑ i : Fin 3, DP g2 i t • (JL).comp (EH i t))+
    (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t •
      ((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp (EH j t)+
        (EL i t).comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)))+
    t.1.2.2^2 • (∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t • (EL i t).comp (EH j t))
local notation "PHI" => zeroParameterFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def zeroHessianFactor (g2 : MatrixField) (mk : Fin 3 × Fin 3) (t : Tpar) : Hi →L[ℝ] Neg :=
  ∑ i : Fin 3, ∑ j : Fin 3, QP g2 i j t •
    ((XP i t) mk.1 • (JL).comp (fderiv ℝ (EH j) t (hessianTangent mk.2)))
local notation "PSI" => zeroHessianFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Genuine smooth parameter factors on the exact original common room. -/
theorem canonical_zero_factor_germs
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (t : Tpar) (ht : t ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (PHI g2) t ∧ ∀ mk, ContDiffAt ℝ ∞ (PSI g2 mk) t := by
  have hqx : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    (contDiff_fst.fst).prodMk (contDiff_fst.snd.fst)
  have hQ (i j : Fin 3) : ContDiffAt ℝ ∞ (fun z : Tpar => QP g2 i j z) t :=
    ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp hqx).contDiffAt
  have hb (i : Fin 3) : ContDiffAt ℝ ∞ (fun z : Tpar => DP g2 i z) t :=
    ((contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp hqx).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiff_fst.snd.snd.contDiffAt
  have hH (j : Fin 3) := Cm.germHigh j t ht
  have hL (i : Fin 3) := Cm.germLow i t ht
  have hDH (j : Fin 3) : ContDiffAt ℝ ∞ (fderiv ℝ (EH j)) t :=
    (hH j).fderiv_right (m := ∞) (by simp)
  have jl : ContDiffAt ℝ ∞ (fun _ : Tpar => (JL : Half →L[ℝ] Neg)) t := contDiffAt_const
  have hl (i : Fin 3) : ContDiffAt ℝ ∞ (fun z : Tpar => z.2 (XP i z)) t :=
    contDiff_snd.contDiffAt.clm_apply (contDiff_parameterGramFrame g hg L i).contDiffAt
  have hR (i j : Fin 3) : ContDiffAt ℝ ∞ (ZR i j) t := by
    unfold regularZeroRow
    exact (((jl.clm_comp ((hDH j).clm_apply (contDiff_basicTangent_gram g hg L i).contDiffAt)).add
      ((contDiff_parameterLowerAngular g hg L i).contDiffAt.clm_comp (hH j))).add
      ((hL i).clm_comp (contDiff_parameterHighAngular g hg L j).contDiffAt)).sub
      (ContDiffAt.sum fun k _ => (contDiff_parameterConnection g hg L i k j).contDiffAt.smul
        (jl.clm_comp (hH k)))
  have hLog (i j : Fin 3) : ContDiffAt ℝ ∞ (ZL i j) t := by
    unfold logarithmicZeroRow
    exact (((hl i).smul (contDiffAt_const.clm_comp (hH j))).add
      ((hl j).smul ((hL i).clm_comp contDiffAt_const))).add ((hl i).smul (jl.clm_comp (hH j)))
  constructor
  · unfold zeroParameterFactor
    exact ((((hr.smul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (hQ i j).smul (hR i j))).add
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (hQ i j).smul (hLog i j))).add
      (hr.smul (ContDiffAt.sum fun i _ => (hb i).smul (jl.clm_comp (hH i))))).add
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (hQ i j).smul
        ((contDiffAt_const.clm_comp (hH j)).add ((hL i).clm_comp contDiffAt_const)))).add
      ((hr.pow 2).smul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (hQ i j).smul ((hL i).clm_comp (hH j))))
  · intro mk
    unfold zeroHessianFactor
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    have hXi : ContDiffAt ℝ ∞ (fun z => (XP i z) mk.1) t :=
      ((EuclideanSpace.proj (𝕜 := ℝ) mk.1).contDiff.comp (contDiff_parameterGramFrame g hg L i)).contDiffAt
    exact (hQ i j).smul (hXi.smul (jl.clm_comp ((hDH j).clm_apply contDiffAt_const)))

/-- Exact clearing of the original horizontal logarithmic radius derivative. -/
lemma radius_mul_horizontalLogDerivative (g : MatrixField) (L q : ℝ)
    (RR : R3 → ℝ) (hR : ContDiff ℝ ∞ RR) (x : R3) (hr : RR x ≠ 0) (i : Fin 3) :
    RR x*referenceRadiusHorizontalLogDerivative g L q RR x i =
      fderiv ℝ RR x (referenceMetricGramFrame g L (q,x) i) := by
  unfold referenceRadiusHorizontalLogDerivative
  rw [ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x i,
    fderiv.log (hR.differentiable (by simp) x) hr]
  simp only [smul_apply,smul_eq_mul]
  rw [←mul_assoc,mul_inv_cancel₀ hr,one_mul]

local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Literal profileHigh chain rule, before the coefficient algebra or any norm estimate. -/
lemma fderiv_profileHigh_factor_split (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (x : R3) (i j : Fin 3)
    (hf : DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) x)) :
    fderiv ℝ (PH δr Ar p q j) x (XP i ((Tq δr Ar p q) x)) =
      fderiv ℝ (EH j) ((Tq δr Ar p q) x)
        (basicTangent ((Tq δr Ar p q) x) (XP i ((Tq δr Ar p q) x)))+
      ∑ mk : Fin 3 × Fin 3,
        hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x) •
          ((XP i ((Tq δr Ar p q) x)) mk.1 •
            fderiv ℝ (EH j) ((Tq δr Ar p q) x) (hessianTangent mk.2)) := by
  have he : PH δr Ar p q j = fun y => EH j ((q,(y,referenceRadius δr Ar p L y)),
      fderiv ℝ (referenceRadius δr Ar p L) y) := by
    funext y
    unfold ActualHigherSCoefficientExtraction.profileHigh ActualHigherSFormation.higherSParam
    rfl
  have hd := congrArg (fun f : R3 → (Hi →L[ℝ] Half) =>
    fderiv ℝ f x (XP i ((Tq δr Ar p q) x))) he
  have hc := fderiv_radiusComposite_split (referenceRadius δr Ar p L)
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr)
    (EH j) q x (XP i ((Tq δr Ar p q) x)) hf
  exact hd.trans hc

end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
