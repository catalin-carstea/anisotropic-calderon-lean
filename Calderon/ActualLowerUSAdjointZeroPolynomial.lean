import Calderon.ActualLowerUSAdjointCoefficients
import Calderon.ActualLowerUSWeightedScalarJets
import Calderon.ActualFiniteHarmonicModelCQuadraticMassBounds
import Calderon.ActualFiniteHarmonicModelWPolynomialMassBounds
import Calderon.ActualFiniteHarmonicModelWeightedYAngularMassBounds
import Calderon.ActualGeneratorEPairedGainedEndpoints

/-!
Exact original lower-only zero polynomial and zeroth scalar coefficient mass.
All primitive budgets are produced internally; no first-jet mass machinery.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  DirichletFamily.DriftBootstrap ActualRetainedGeneratorMultiplierGains
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftDefectWeightedJets NormalizedPrincipalMetric
  NormalizedPrincipalMetricSmooth ReferenceDensityBounds ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint PrincipalCommutator ConformalDepth SmoothMetricFrame
  MovingFrameConnection AmbientReferenceRaising AmbientReferenceCovariantCore
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDSpectralTransport
  ActualReferenceDDHigherGeometryJets

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev lowerZeroPolynomialFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] lowerZeroPolynomialFunction

/-- Identity followed by the existing degree/rotation/lowering index. -/
abbrev LowerCoreAngularGeneratorIndex := Unit ⊕ (Generator ⊕ Fin 3)

/-- Rotation has the exact generatorSharp sign; there is no raising branch. -/
def lowerCoreAngularGenerator (hF : SphereFischerInner) : LowerCoreAngularGeneratorIndex →
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD)
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl (Sum.inl (b,c))) => -coreRotation hO hD b c
  | Sum.inr (Sum.inl (Sum.inr _)) => coreDegree hO hD
  | Sum.inr (Sum.inr a) => coreDerivative hO hD hF a

private abbrev TraceCoreAngularIndex := Unit ⊕ Generator
private def traceCoreAngularGenerator : TraceCoreAngularIndex →
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD)
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl (b,c)) => coreRotation hO hD b c
  | Sum.inr (Sum.inr _) => coreDegree hO hD
private def traceCoreAngularIndex : TraceCoreAngularIndex → CoreAngularGeneratorIndex
  | Sum.inl _ => Sum.inr (Sum.inr (Sum.inr false))
  | Sum.inr (Sum.inl bc) => Sum.inr (Sum.inr (Sum.inl bc))
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr (Sum.inr true))

private lemma traceGeneratorCentral (hF : SphereFischerInner) (i : TraceCoreAngularIndex) :
    ScalarCentral hO hD (traceCoreAngularGenerator hO hD i) := by
  have h := scalarCentral_coreAngularGenerator hO hD hF (traceCoreAngularIndex i)
  cases i with
  | inl u => cases u; exact h
  | inr v => cases v with
    | inl bc => exact h
    | inr u => cases u; exact h

private lemma traceGeneratorExp (hF : SphereFischerInner) (i : TraceCoreAngularIndex) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (traceCoreAngularGenerator hO hD i) x 1 := by
  simpa only [coreScalar_const_mul_eq_smul,one_smul,abs_one] using
    hasCoreScalarExpansionBound_single hO hD (traceCoreAngularGenerator hO hD) i
      (fun _ => (1:ℝ)) contDiff_const x

private lemma traceScalar (hF : SphereFischerInner) (c : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (coreScalar hO hD c hc) x |c x| := by
  simpa only [traceCoreAngularGenerator,mul_one] using
    hasCoreScalarExpansionBound_single hO hD (traceCoreAngularGenerator hO hD)
      (Sum.inl ()) c hc x

private lemma traceLinearToQuad (hF : SphereFischerInner)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex =>
        traceCoreAngularGenerator hO hD ij.1 * traceCoreAngularGenerator hO hD ij.2) A x C := by
  simpa only [mul_one] using hasCoreScalarExpansionBound_product hO hD
    (traceCoreAngularGenerator hO hD) (traceCoreAngularGenerator hO hD)
    (traceGeneratorCentral hO hD hF) A 1 x C 1 hA
    (traceGeneratorExp hO hD hF (Sum.inl ()) x)

private lemma traceConnectionExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeReferenceConnectionAction hO hD g hg L lam a) x
      (nativeReferenceConnectionCoefficientMass g L lam a x) := by
  let G := traceCoreAngularGenerator hO hD
  let c (b d : Fin 3) (y : R3) := referenceFrameConnectionCoefficient g L lam y
    (referenceMetricGramFrame g L (lam,y) a) b d
  have hc (b d : Fin 3) : ContDiff ℝ ∞ (c b d) :=
    AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field
      g hg L lam _ (contDiff_referenceMetricGramFrame_slice g hg L lam a) b d
  have he (b d : Fin 3) : HasCoreScalarExpansionBound hO hD G
      (coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d) x |c b d x| :=
    hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inl (b,d)))
      (c b d) (hc b d) x
  have hs := hasCoreScalarExpansionBound_sum hO hD G Finset.univ
    (fun b => ∑ d : Fin 3, coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d)
    x (fun b => ∑ d : Fin 3, |c b d x|)
    (fun b _ => hasCoreScalarExpansionBound_sum hO hD G Finset.univ
      (fun d => coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d)
      x (fun d => |c b d x|) (fun d _ => he b d))
  have ht := hasCoreScalarExpansionBound_smul hO hD G _ x _ (1/2 : ℝ) hs
  simpa only [nativeReferenceConnectionAction,nativeReferenceConnectionCoefficientMass,G,c,
    abs_of_pos (by norm_num : 0 < (1/2 : ℝ))] using ht

private lemma traceProfileExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a) x
      |referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x| := by
  exact traceScalar hO hD hF _ _ x

private lemma traceConnectionDerivativeExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a z : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeReferenceConnectionFrameDerivative hO hD g hg L lam a z) x
      (nativeReferenceConnectionDerivativeMass g L lam a z x) := by
  let G := traceCoreAngularGenerator hO hD
  let c (b d : Fin 3) := referenceFrameDerivative g L lam a
    (fun y => referenceFrameConnectionCoefficient g L lam y
      (referenceMetricGramFrame g L (lam,y) z) b d)
  have hc (b d : Fin 3) : ContDiff ℝ ∞ (c b d) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field
        g hg L lam _ (contDiff_referenceMetricGramFrame_slice g hg L lam z) b d)
  have he (b d : Fin 3) : HasCoreScalarExpansionBound hO hD G
      (coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d) x |c b d x| :=
    hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inl (b,d)))
      (c b d) (hc b d) x
  have hs := hasCoreScalarExpansionBound_sum hO hD G Finset.univ
    (fun b => ∑ d : Fin 3, coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d)
    x (fun b => ∑ d : Fin 3, |c b d x|)
    (fun b _ => hasCoreScalarExpansionBound_sum hO hD G Finset.univ
      (fun d => coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d)
      x (fun d => |c b d x|) (fun d _ => he b d))
  have ht := hasCoreScalarExpansionBound_smul hO hD G _ x _ (1/2 : ℝ) hs
  simpa only [nativeReferenceConnectionFrameDerivative,nativeReferenceConnectionDerivativeMass,G,c,
    abs_of_pos (by norm_num : 0 < (1/2 : ℝ))] using ht

private lemma traceWeightedZeroExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeReferenceConnectionAction hO hD g hg L lam a+
        nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*coreDegree hO hD) x
      (nativeReferenceWeightedZeroRawMass g L lam δ R p a x) := by
  apply hasCoreScalarExpansionBound_add hO hD
  · exact traceConnectionExp hO hD hF g hg L lam a x
  · have ht := hasCoreScalarExpansionBound_single hO hD (traceCoreAngularGenerator hO hD)
      (Sum.inr (Sum.inr ()))
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      (contDiff_referenceFrameDerivative g hg L lam a _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)) x
    exact ht

private lemma traceCovectorZeroExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a b : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex =>
        traceCoreAngularGenerator hO hD ij.1*traceCoreAngularGenerator hO hD ij.2)
      (nativeReferenceCovectorZeroRawAction hO hD g hg L lam δ R p hδ hR a b) x
      (nativeReferenceCovectorZeroRawMass g L lam δ R p a b x) := by
  let G := traceCoreAngularGenerator hO hD
  let Q := fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex => G ij.1*G ij.2
  let A (c : Fin 3) := nativeReferenceConnectionAction hO hD g hg L lam c
  let P (c : Fin 3) := nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR c
  let Z (c : Fin 3) := A c+P c*coreDegree hO hD
  let q (c : Fin 3) := referenceFrameDerivative g L lam c (fun y => Real.log (referenceRadius δ R p L y))
  have hq (c : Fin 3) : ContDiff ℝ ∞ (q c) :=
    contDiff_referenceFrameDerivative g hg L lam c _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  let gamma (c : Fin 3) (y : R3) := referenceFrameConnectionCoefficient g L lam y
    (referenceMetricGramFrame g L (lam,y) a) c b
  have hgamm (c : Fin 3) : ContDiff ℝ ∞ (gamma c) :=
    contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam a) c b
  let M (c : Fin 3) := nativeReferenceWeightedZeroRawMass g L lam δ R p c x
  have hz (c : Fin 3) : HasCoreScalarExpansionBound hO hD G (Z c) x (M c) :=
    traceWeightedZeroExp hO hD hF g hg L lam δ R p hδ hR c x
  have hdA := traceLinearToQuad hO hD hF _ x _
    (traceConnectionDerivativeExp hO hD hF g hg L lam a b x)
  have hdP : HasCoreScalarExpansionBound hO hD Q
      (nativeReferenceProfileFrameDerivative hO hD g hg L lam δ R p hδ hR a b*coreDegree hO hD) x
      |referenceFrameDerivative g L lam a (q b) x| := by
    apply traceLinearToQuad hO hD hF
    exact hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inr ()))
      (referenceFrameDerivative g L lam a (q b))
      (contDiff_referenceFrameDerivative g hg L lam a _ (hq b)) x
  have hprod := hasCoreScalarExpansionBound_product hO hD G G
    (traceGeneratorCentral hO hD hF) (A a) (Z b) x _ _
    (traceConnectionExp hO hD hF g hg L lam a x) (hz b)
  have hsum : HasCoreScalarExpansionBound hO hD Q
      (∑ c : Fin 3, coreScalar hO hD (gamma c) (hgamm c)*Z c) x
      (∑ c : Fin 3, |gamma c x| *M c) := by
    apply traceLinearToQuad hO hD hF
    apply hasCoreScalarExpansionBound_sum hO hD
    intro c _
    exact hasCoreScalarExpansionBound_scalar_mul hO hD G (Z c) x (M c) (hz c) (gamma c) (hgamm c)
  have hpz : HasCoreScalarExpansionBound hO hD G (P a*Z b) x (|q a x| *M b) :=
    hasCoreScalarExpansionBound_scalar_mul hO hD G (Z b) x (M b) (hz b) (q a) (hq a)
  have hlast : HasCoreScalarExpansionBound hO hD Q ((P a*Z b)*coreDegree hO hD) x (|q a x| *M b) := by
    have hn := traceGeneratorExp hO hD hF (Sum.inr (Sum.inr ())) x
    simpa only [mul_one] using hasCoreScalarExpansionBound_product hO hD G G
      (traceGeneratorCentral hO hD hF) (P a*Z b) (coreDegree hO hD) x _ 1 hpz hn
  exact hasCoreScalarExpansionBound_add hO hD Q _ _ x _ _
    (hasCoreScalarExpansionBound_sub hO hD Q _ _ x _ _
      (hasCoreScalarExpansionBound_add hO hD Q _ _ x _ _
        (hasCoreScalarExpansionBound_add hO hD Q _ _ x _ _ hdA hdP) hprod) hsum) hlast

private lemma traceTraceZeroExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex =>
        traceCoreAngularGenerator hO hD ij.1*traceCoreAngularGenerator hO hD ij.2)
      (nativeReferenceTraceZeroRawAction hO hD g hg L lam δ R p h hh hδ hR) x
      (nativeReferenceTraceZeroRawMass g L lam δ R p h x) := by
  unfold nativeReferenceTraceZeroRawAction nativeReferenceTraceZeroRawMass
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  apply hasCoreScalarExpansionBound_sum hO hD
  intro b _
  exact hasCoreScalarExpansionBound_scalar_mul hO hD _ _ x _
    (traceCovectorZeroExp hO hD hF g hg L lam δ R p hδ hR a b x)
    _ _

private def traceCoreAngularStar (hF : SphereFischerInner) (i : TraceCoreAngularIndex) :=
  coreAngularGeneratorAdjoint hO hD hF (traceCoreAngularIndex i)

private lemma traceStarExp (hF : SphereFischerInner) (i : TraceCoreAngularIndex) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (traceCoreAngularStar hO hD hF i) x 1 := by
  rcases i with u | (bc | u)
  · cases u
    exact traceGeneratorExp hO hD hF (Sum.inl ()) x
  · simpa only [traceCoreAngularStar,traceCoreAngularIndex,coreAngularGeneratorAdjoint,
      traceCoreAngularGenerator] using hasCoreScalarExpansionBound_neg hO hD
        (traceCoreAngularGenerator hO hD) _ x 1
        (traceGeneratorExp hO hD hF (Sum.inr (Sum.inl bc)) x)
  · cases u
    exact traceGeneratorExp hO hD hF (Sum.inr (Sum.inr ())) x

private lemma traceGeneratorBounds (hF : SphereFischerInner) (i : TraceCoreAngularIndex) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (traceCoreAngularGenerator hO hD i)
      (traceCoreAngularStar hO hD hF i) (coreAngularGeneratorBound hO hD) x := by
  have h := hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (traceCoreAngularIndex i) x
  rcases i with u | (bc | u)
  · cases u; exact h
  · exact h
  · cases u; exact h

private lemma tracePointwiseAdjointExp (hF : SphereFischerInner)
    (A S : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hadj : ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ y : R3,
      ⟪A F y,G y⟫_ℝ = ⟪F y,S G y⟫_ℝ) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD
      (fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex =>
        traceCoreAngularGenerator hO hD ij.1 * traceCoreAngularGenerator hO hD ij.2) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex =>
        traceCoreAngularGenerator hO hD ij.1 * traceCoreAngularGenerator hO hD ij.2) S x C := by
  obtain ⟨c,hc,he,hm⟩ := hA
  let G := traceCoreAngularGenerator hO hD
  let GS := traceCoreAngularStar hO hD hF
  let T (ij : TraceCoreAngularIndex × TraceCoreAngularIndex) := GS ij.2 * GS ij.1
  let AS := coreScalarCombination hO hD T c hc
  have hASadj (F G0 : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      ⟪A F y,G0 y⟫_ℝ = ⟪F y,AS G0 y⟫_ℝ := by
    rw [he]
    dsimp only [AS,coreScalarCombination]
    simp only [LinearMap.sum_apply,Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
      Submodule.coe_mk,Submodule.coe_sum,Finset.sum_apply,sum_inner,inner_sum,
      real_inner_smul_left,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro ij _
    congr 1
    exact coreAngular_product_inner_adjoint hO hD _ _ _ _ _ _ y
      (traceGeneratorBounds hO hD hF ij.1 y) (traceGeneratorBounds hO hD hF ij.2 y) F G0
  have hEq : S=AS := by
    apply coreEnd_eq_of_pointwise_inner_eq hO hD
    intro F G0 y
    calc
      ⟪S F y,G0 y⟫_ℝ = ⟪G0 y,S F y⟫_ℝ := real_inner_comm _ _
      _ = ⟪A G0 y,F y⟫_ℝ := (hadj G0 F y).symm
      _ = ⟪G0 y,AS F y⟫_ℝ := hASadj G0 F y
      _ = ⟪AS F y,G0 y⟫_ℝ := real_inner_comm _ _
  rw [hEq]
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ C _ hm
  unfold AS coreScalarCombination
  apply hasCoreScalarExpansionBound_sum hO hD
  intro ij _
  have ht : HasCoreScalarExpansionBound hO hD
      (fun kl : TraceCoreAngularIndex × TraceCoreAngularIndex => G kl.1*G kl.2) (T ij) x 1 := by
    simpa only [one_mul,T,G,GS] using hasCoreScalarExpansionBound_product hO hD G G
      (traceGeneratorCentral hO hD hF) _ _ x 1 1
      (traceStarExp hO hD hF ij.2 x) (traceStarExp hO hD hF ij.1 x)
  simpa only [mul_one,G] using
    hasCoreScalarExpansionBound_scalar_mul hO hD _ (T ij) x 1 ht (c ij) (hc ij)

private lemma lowerGeneratorCentral (hF : SphereFischerInner) (i : LowerCoreAngularGeneratorIndex) :
    ScalarCentral hO hD (lowerCoreAngularGenerator hO hD hF i) := by
  rcases i with u | ((bc | u) | a)
  · cases u
    exact scalarCentral_coreAngularGenerator hO hD hF (Sum.inr (Sum.inr (Sum.inr false)))
  · change ScalarCentral hO hD (-coreRotation hO hD bc.1 bc.2)
    have he : (-1 : ℝ) • coreRotation hO hD bc.1 bc.2 = -coreRotation hO hD bc.1 bc.2 := by
      module
    rw [← he]
    exact scalarCentral_smul hO hD (-1 : ℝ)
      (coreRotation hO hD bc.1 bc.2) (scalarCentral_coreRotation hO hD bc.1 bc.2)
  · cases u
    exact scalarCentral_coreAngularGenerator hO hD hF (Sum.inr (Sum.inr (Sum.inr true)))
  · exact scalarCentral_coreAngularGenerator hO hD hF (Sum.inl a)

private lemma lowerGeneratorExp (hF : SphereFischerInner)
    (i : LowerCoreAngularGeneratorIndex) (x : R3) :
    HasCoreScalarExpansionBound hO hD (lowerCoreAngularGenerator hO hD hF)
      (lowerCoreAngularGenerator hO hD hF i) x 1 := by
  simpa only [coreScalar_const_mul_eq_smul,one_smul,abs_one] using
    hasCoreScalarExpansionBound_single hO hD (lowerCoreAngularGenerator hO hD hF) i
      (fun _ => (1:ℝ)) contDiff_const x

private lemma lowerRotationExp (hF : SphereFischerInner) (b c : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (lowerCoreAngularGenerator hO hD hF)
      (coreRotation hO hD b c) x 1 := by
  have hh := hasCoreScalarExpansionBound_smul hO hD
    (lowerCoreAngularGenerator hO hD hF) _ x 1 (-1 : ℝ)
    (lowerGeneratorExp hO hD hF (Sum.inr (Sum.inl (Sum.inl (b,c)))) x)
  have he : (-1 : ℝ) • lowerCoreAngularGenerator hO hD hF
      (Sum.inr (Sum.inl (Sum.inl (b,c)))) = coreRotation hO hD b c := by
    change (-1 : ℝ) • (-coreRotation hO hD b c) = coreRotation hO hD b c
    module
  rw [he] at hh
  simpa only [abs_neg,abs_one,one_mul] using hh

private lemma lowerScalar (hF : SphereFischerInner) (c : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (x : R3) :
    HasCoreScalarExpansionBound hO hD (lowerCoreAngularGenerator hO hD hF)
      (coreScalar hO hD c hc) x |c x| := by
  simpa only [lowerCoreAngularGenerator,mul_one] using
    hasCoreScalarExpansionBound_single hO hD (lowerCoreAngularGenerator hO hD hF)
      (Sum.inl ()) c hc x

private lemma lowerLinearToQuad (hF : SphereFischerInner)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (lowerCoreAngularGenerator hO hD hF) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
        lowerCoreAngularGenerator hO hD hF (Prod.fst ij) * lowerCoreAngularGenerator hO hD hF (Prod.snd ij)) A x C := by
  simpa only [mul_one] using hasCoreScalarExpansionBound_product hO hD
    (lowerCoreAngularGenerator hO hD hF) (lowerCoreAngularGenerator hO hD hF)
    (lowerGeneratorCentral hO hD hF) A 1 x C 1 hA
    (lowerGeneratorExp hO hD hF (Sum.inl ()) x)

private lemma traceQuadToLower (hF : SphereFischerInner)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD
      (fun ij : TraceCoreAngularIndex × TraceCoreAngularIndex =>
        traceCoreAngularGenerator hO hD ij.1 * traceCoreAngularGenerator hO hD ij.2) A x C) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
        lowerCoreAngularGenerator hO hD hF (Prod.fst ij) * lowerCoreAngularGenerator hO hD hF (Prod.snd ij)) A x C := by
  have hT (i : TraceCoreAngularIndex) : HasCoreScalarExpansionBound hO hD
      (lowerCoreAngularGenerator hO hD hF) (traceCoreAngularGenerator hO hD i) x 1 := by
    rcases i with u | (bc | u)
    · cases u; exact lowerGeneratorExp hO hD hF (Sum.inl ()) x
    · exact lowerRotationExp hO hD hF bc.1 bc.2 x
    · cases u; exact lowerGeneratorExp hO hD hF (Sum.inr (Sum.inl (Sum.inr ()))) x
  obtain ⟨c,hc,he,hm⟩ := hA
  rw [he]
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ C _ hm
  unfold coreScalarCombination
  apply hasCoreScalarExpansionBound_sum hO hD
  intro ij _
  have hp : HasCoreScalarExpansionBound hO hD
      (fun kl : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
        lowerCoreAngularGenerator hO hD hF kl.1 * lowerCoreAngularGenerator hO hD hF kl.2)
      (traceCoreAngularGenerator hO hD ij.1 * traceCoreAngularGenerator hO hD ij.2) x 1 := by
    simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD
      (lowerCoreAngularGenerator hO hD hF) (lowerCoreAngularGenerator hO hD hF)
      (lowerGeneratorCentral hO hD hF) _ _ x 1 1 (hT ij.1) (hT ij.2)
  simpa only [mul_one] using hasCoreScalarExpansionBound_scalar_mul hO hD _ _ x 1
    hp (c ij) (hc ij)

private lemma lowerTraceAdjointExp (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q dr Ar : ℝ) (p : ℕ) (h : MatrixField)
    (hh : ContDiff ℝ ∞ h) (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
        lowerCoreAngularGenerator hO hD hF (Prod.fst ij) * lowerCoreAngularGenerator hO hD hF (Prod.snd ij))
      (nativeReferenceTraceZeroAdjointRawAction hO hD g hg L q dr Ar p h hh hdr hAr) x
      (nativeReferenceTraceZeroRawMass g L q dr Ar p h x) := by
  apply traceQuadToLower hO hD hF
  exact tracePointwiseAdjointExp hO hD hF _ _
    (nativeReferenceTraceZeroRawAction_inner_adjoint hO hD g hg L q dr Ar p h hh hdr hAr)
    x _ (traceTraceZeroExp hO hD hF g hg L q dr Ar p h hh hdr hAr x)
private lemma traceYAngularExp
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeWeightedYAngularPart hO hD g hg L lam δ R p h hh hδ hR) x
      (nativeWeightedYAngularPartMass g L lam δ R p h x) := by
  unfold nativeWeightedYAngularPart nativeWeightedYAngularPartMass
  dsimp only
  have hn (B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) : (-1 : ℝ) • B = -B := neg_one_smul ℝ B
  rw [hn]
  apply hasCoreScalarExpansionBound_neg hO hD
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro j _
  apply hasCoreScalarExpansionBound_sub hO hD
  · exact hasCoreScalarExpansionBound_single hO hD _ (Sum.inr (Sum.inr ())) _ _ x
  · apply hasCoreScalarExpansionBound_sum hO hD
    intro s _
    apply hasCoreScalarExpansionBound_sum hO hD
    intro t _
    exact hasCoreScalarExpansionBound_single hO hD _ (Sum.inr (Sum.inl (s,t))) _ _ x

private lemma traceDriftExp
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeDriftZeroRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR) x
      (nativeDriftZeroRawMass g1 g2 L lam δ R p x) := by
  unfold nativeDriftZeroRawAction nativeDriftZeroRawMass
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  exact hasCoreScalarExpansionBound_scalar_mul hO hD _ _ x _
    (traceWeightedZeroExp hO hD hF g1 hg1 L lam δ R p hδ hR a x) _ _

private lemma traceDriftConnectionExp
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD (traceCoreAngularGenerator hO hD)
      (nativeDriftConnectionRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR) x
      (nativeDriftZeroRawMass g1 g2 L lam δ R p x) := by
  unfold nativeDriftConnectionRawAction nativeDriftZeroRawMass
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (traceConnectionExp hO hD hF g1 hg1 L lam a x)
  unfold nativeReferenceWeightedZeroRawMass
  exact le_add_of_nonneg_right (abs_nonneg _)

variable (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ)
  (hdr : 0 < dr) (hAr : 0 < Ar)
local notation "hRef" => referenceNormalizedPrincipalDifference g g2 L q
local notation "hhRef" => ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference
  g g2 hg hg2 L q
local notation "pSmooth" a:max => contDiff_physicalMixedProfileCoefficient g hg L q dr Ar p hRef hdr hAr
  (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q i j) a
local notation "kSmooth" a:max b:max c:max => contDiff_physicalMixedConnectionCoefficient g hg L q hRef
  (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q i j) a b c
local notation "uSmooth" a:max b:max => contDiff_physicalPureAngularCoefficient g hg L q dr Ar p hRef hdr hAr
  (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q i j) a b
local notation "dSmooth" a:max => contDiff_physicalMixedDensityCorrection g hg L q hRef
  (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q i j) a
local notation "Ps" a:max => coreScalar hO hD (physicalMixedProfileCoefficient g L q dr Ar p hRef a) (pSmooth a)
local notation "Ks" a:max b:max c:max => coreScalar hO hD (physicalMixedConnectionCoefficient g L q hRef a b c) (kSmooth a b c)
local notation "Us" a:max b:max => coreScalar hO hD (physicalPureAngularCoefficient g L q dr Ar p hRef a b) (uSmooth a b)
local notation "Ds" a:max => coreScalar hO hD (physicalMixedDensityCorrection g L q hRef a) (dSmooth a)
local notation "LD" a:max => coreDerivative hO hD hF a
local notation "NN" => coreDegree hO hD
local notation "YS" => nativeWeightedYScalarPart hO hD g hg L q dr Ar p hRef hhRef hdr hAr
local notation "YA" => nativeWeightedYAngularPart hO hD g hg L q dr Ar p hRef hhRef hdr hAr
local notation "DV" => coreScalar hO hD (normalizedSecondDriftDensityDivergence g g2 L q dr Ar p)
  (contDiff_normalizedSecondDriftDensityDivergence g g2 hg hg2 L q dr Ar p hdr hAr)
local notation "DR0" => nativeDriftZeroRawAction hO hD g g2 hg hg2 L q dr Ar p hdr hAr
local notation "DRC" => nativeDriftConnectionRawAction hO hD g g2 hg hg2 L q dr Ar p hdr hAr
local notation "TR" => nativeReferenceTraceZeroAdjointRawAction hO hD g hg L q dr Ar p hRef hhRef hdr hAr
local notation "LG" => lowerCoreAngularGenerator hO hD hF
local notation "LQ" => (fun ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
  lowerCoreAngularGenerator hO hD hF (Prod.fst ij) * lowerCoreAngularGenerator hO hD hF (Prod.snd ij))

/-- Explicit original lower-only polynomial. Every forward raising word has
cancelled with its exact W-polynomial partner; order of the lowering words is retained. -/
def nativeULowerAdjointZeroLowerPolynomial : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  TR + (∑ a : Fin 3, (Ds a) * LD a) +
    (∑ a : Fin 3, (Ps a) * (LD a * (NN-1))) -
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (Ks a b c) * (coreRotation hO hD b c * LD a)) +
    (∑ a : Fin 3, ∑ b : Fin 3, (Us a b) * (LD b * LD a)) +
    DR0 - (2 : ℝ) • DRC + YS + YA - DV

/-- Typed conversion of the original dependent native W definition before algebra. -/
private lemma nativeWPolynomialPart_eq_lower_words :
    nativeWPolynomialPart hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr =
    (TR-nativeReferenceTraceZeroRawAction hO hD g hg L q dr Ar p hRef hhRef hdr hAr) +
    (∑ a : Fin 3, (Ds a)*LD a) +
    (∑ a : Fin 3, (Ps a)*(LD a*(NN-1)-coreRaising hO hD hF a*NN)) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (Ks a b c)*(-(coreRotation hO hD b c*LD a)-coreRaising hO hD hF a*coreRotation hO hD b c)) +
    (∑ a : Fin 3, ∑ b : Fin 3, (Us a b)*(LD b*LD a-coreRaising hO hD hF a*coreRaising hO hD hF b)) +
    (-2 : ℝ) • DRC := by
  rfl

/-- Literal raising cancellation, with scalar Y and drift density retained. -/
theorem nativeULowerAdjointZeroCoefficient_eq_lower_polynomial :
    nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr =
      nativeULowerAdjointZeroLowerPolynomial hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr := by
  unfold nativeULowerAdjointZeroCoefficient
  rw [nativeC_eq_raw_quadratic_coefficients hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr,
    nativeWeightedY_eq_scalar_add_angular hO hD g hg L q dr Ar p hRef hhRef hdr hAr]
  rw [nativeWPolynomialPart_eq_lower_words hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr]
  unfold nativeULowerAdjointZeroLowerPolynomial
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_smul,
    Submodule.coe_sum,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,
    coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]
  simp only [smul_sub,smul_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  module

/-- An explicit safe mass for the displayed reduced polynomial, never a residual. -/
def nativeULowerAdjointZeroLowerMass (x : R3) : ℝ :=
  nativeReferenceTraceZeroRawMass g L q dr Ar p hRef x +
    (∑ a : Fin 3, |physicalMixedDensityCorrection g L q hRef a x|) +
    (∑ a : Fin 3, 2*|physicalMixedProfileCoefficient g L q dr Ar p hRef a x|) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, |physicalMixedConnectionCoefficient g L q hRef a b c x|) +
    (∑ a : Fin 3, ∑ b : Fin 3, |physicalPureAngularCoefficient g L q dr Ar p hRef a b x|) +
    3*nativeDriftZeroRawMass g g2 L q dr Ar p x +
    |nativeWeightedYScalarCoefficient g g2 L q dr Ar p x| +
    nativeWeightedYAngularPartMass g L q dr Ar p hRef x +
    |normalizedSecondDriftDensityDivergence g g2 L q dr Ar p x|

/-- Exact restricted coefficient certificate: the global smooth scalar
representation uses only identity, degree, minus-rotation and lowering. -/
theorem hasCoreScalarExpansionBound_nativeULowerAdjointZero_lower (x : R3) :
    HasCoreScalarExpansionBound hO hD LQ
      (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) x
      (nativeULowerAdjointZeroLowerMass g g2 L q dr Ar p x) := by
  have hL (a : Fin 3) : HasCoreScalarExpansionBound hO hD LG (LD a) x 1 :=
    lowerGeneratorExp hO hD hF (Sum.inr (Sum.inr a)) x
  have hN : HasCoreScalarExpansionBound hO hD LG NN x 1 :=
    lowerGeneratorExp hO hD hF (Sum.inr (Sum.inl (Sum.inr ()))) x
  have hId : HasCoreScalarExpansionBound hO hD LG 1 x 1 :=
    lowerGeneratorExp hO hD hF (Sum.inl ()) x
  have hTr := lowerTraceAdjointExp hO hD hF g hg L q dr Ar p hRef hhRef hdr hAr x
  have hDc : HasCoreScalarExpansionBound hO hD LQ (∑ a : Fin 3, (Ds a)*LD a) x
      (∑ a : Fin 3, |physicalMixedDensityCorrection g L q hRef a x|) := by
    apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    apply lowerLinearToQuad hO hD hF
    simpa only [mul_one] using hasCoreScalarExpansionBound_scalar_mul hO hD LG _ x 1 (hL a)
      (physicalMixedDensityCorrection g L q hRef a) (dSmooth a)
  have hP : HasCoreScalarExpansionBound hO hD LQ (∑ a : Fin 3, (Ps a)*(LD a*(NN-1))) x
      (∑ a : Fin 3, 2*|physicalMixedProfileCoefficient g L q dr Ar p hRef a x|) := by
    apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    have hn : HasCoreScalarExpansionBound hO hD LG (NN-1) x 2 := by
      convert hasCoreScalarExpansionBound_sub hO hD LG NN 1 x 1 1 hN hId using 1 <;> norm_num
    have hp : HasCoreScalarExpansionBound hO hD LQ (LD a*(NN-1)) x 2 := by
      simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD LG LG
        (lowerGeneratorCentral hO hD hF) _ _ x 1 2 (hL a) hn
    simpa only [mul_comm] using hasCoreScalarExpansionBound_scalar_mul hO hD LQ _ x 2 hp
      (physicalMixedProfileCoefficient g L q dr Ar p hRef a) (pSmooth a)
  have hK : HasCoreScalarExpansionBound hO hD LQ
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (Ks a b c)*(coreRotation hO hD b c*LD a)) x
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, |physicalMixedConnectionCoefficient g L q hRef a b c x|) := by
    apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    apply hasCoreScalarExpansionBound_sum hO hD
    intro b _
    apply hasCoreScalarExpansionBound_sum hO hD
    intro c _
    have hp : HasCoreScalarExpansionBound hO hD LQ (coreRotation hO hD b c*LD a) x 1 := by
      simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD LG LG
        (lowerGeneratorCentral hO hD hF) _ _ x 1 1 (lowerRotationExp hO hD hF b c x) (hL a)
    simpa only [mul_one] using hasCoreScalarExpansionBound_scalar_mul hO hD LQ _ x 1 hp
      (physicalMixedConnectionCoefficient g L q hRef a b c) (kSmooth a b c)
  have hU : HasCoreScalarExpansionBound hO hD LQ
      (∑ a : Fin 3, ∑ b : Fin 3, (Us a b)*(LD b*LD a)) x
      (∑ a : Fin 3, ∑ b : Fin 3, |physicalPureAngularCoefficient g L q dr Ar p hRef a b x|) := by
    apply hasCoreScalarExpansionBound_sum hO hD
    intro a _
    apply hasCoreScalarExpansionBound_sum hO hD
    intro b _
    have hp : HasCoreScalarExpansionBound hO hD LQ (LD b*LD a) x 1 := by
      simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD LG LG
        (lowerGeneratorCentral hO hD hF) _ _ x 1 1 (hL b) (hL a)
    simpa only [mul_one] using hasCoreScalarExpansionBound_scalar_mul hO hD LQ _ x 1 hp
      (physicalPureAngularCoefficient g L q dr Ar p hRef a b) (uSmooth a b)
  have hDr0 : HasCoreScalarExpansionBound hO hD LQ DR0 x
      (nativeDriftZeroRawMass g g2 L q dr Ar p x) :=
    traceQuadToLower hO hD hF _ x _ (traceLinearToQuad hO hD hF _ x _
      (traceDriftExp hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr x))
  have hDrc : HasCoreScalarExpansionBound hO hD LQ ((2:ℝ) • DRC) x
      (2*nativeDriftZeroRawMass g g2 L q dr Ar p x) := by
    have hh := traceQuadToLower hO hD hF _ x _ (traceLinearToQuad hO hD hF _ x _
      (traceDriftConnectionExp hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr x))
    simpa only [abs_of_pos (by norm_num : 0<(2:ℝ))] using
      hasCoreScalarExpansionBound_smul hO hD LQ DRC x _ 2 hh
  have hYs : HasCoreScalarExpansionBound hO hD LQ YS x
      |nativeWeightedYScalarCoefficient g g2 L q dr Ar p x| := by
    rw [nativeWeightedYScalarPart_eq_coefficient hO hD g g2 hg hg2 L q dr Ar p hdr hAr]
    exact lowerLinearToQuad hO hD hF _ x _ (lowerScalar hO hD hF _ _ x)
  have hYa : HasCoreScalarExpansionBound hO hD LQ YA x
      (nativeWeightedYAngularPartMass g L q dr Ar p hRef x) :=
    traceQuadToLower hO hD hF _ x _ (traceLinearToQuad hO hD hF _ x _
      (traceYAngularExp hO hD hF g hg L q dr Ar p hRef hhRef hdr hAr x))
  have hDv : HasCoreScalarExpansionBound hO hD LQ DV x
      |normalizedSecondDriftDensityDivergence g g2 L q dr Ar p x| :=
    lowerLinearToQuad hO hD hF _ x _ (lowerScalar hO hD hF _ _ x)
  rw [nativeULowerAdjointZeroCoefficient_eq_lower_polynomial hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr]
  unfold nativeULowerAdjointZeroLowerPolynomial nativeULowerAdjointZeroLowerMass
  have hAll := hasCoreScalarExpansionBound_sub hO hD LQ _ _ x _ _
    (hasCoreScalarExpansionBound_add hO hD LQ _ _ x _ _
      (hasCoreScalarExpansionBound_add hO hD LQ _ _ x _ _
        (hasCoreScalarExpansionBound_sub hO hD LQ _ _ x _ _
          (hasCoreScalarExpansionBound_add hO hD LQ _ _ x _ _
            (hasCoreScalarExpansionBound_add hO hD LQ _ _ x _ _
              (hasCoreScalarExpansionBound_sub hO hD LQ _ _ x _ _
                (hasCoreScalarExpansionBound_add hO hD LQ _ _ x _ _
                  (hasCoreScalarExpansionBound_add hO hD LQ _ _ x _ _ hTr hDc) hP) hK) hU) hDr0) hDrc) hYs) hYa) hDv
  convert hAll using 1 <;> ring
private lemma nativeULowerAdjointZeroLowerMass_le_original_budget
    (g g2 : MatrixField) (L q dr Ar : ℝ) (p : ℕ) (x : R3) :
    nativeULowerAdjointZeroLowerMass g g2 L q dr Ar p x ≤
      nativeCQuadraticExpansionMass g g2 L q dr Ar p x +
      nativeWPolynomialPartMass g g2 L q dr Ar p x +
      |nativeWeightedYScalarCoefficient g g2 L q dr Ar p x| +
      nativeWeightedYAngularPartMass g L q dr Ar p
        (referenceNormalizedPrincipalDifference g g2 L q) x +
      |normalizedSecondDriftDensityDivergence g g2 L q dr Ar p x| := by
  let h := referenceNormalizedPrincipalDifference g g2 L q
  have hTr : 0 ≤ nativeReferenceTraceZeroRawMass g L q dr Ar p h x := by
    dsimp only [nativeReferenceTraceZeroRawMass,nativeReferenceCovectorZeroRawMass,
      nativeReferenceConnectionDerivativeMass,nativeReferenceConnectionCoefficientMass,
      nativeReferenceWeightedZeroRawMass]
    positivity
  have hP : 0 ≤ ∑ a : Fin 3, |physicalMixedProfileCoefficient g L q dr Ar p h a x| := by positivity
  have hK : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      |physicalMixedConnectionCoefficient g L q h a b c x| := by positivity
  have hU : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3,
      |physicalPureAngularCoefficient g L q dr Ar p h a b x| := by positivity
  unfold nativeULowerAdjointZeroLowerMass nativeCQuadraticExpansionMass nativeWPolynomialPartMass
  dsimp only
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  dsimp only [h] at hTr hP hK hU
  nlinarith

/-- The original hypotheses produce one restricted lower-only coefficient-mass
constant before dilation, every profile, every point and all angular sizes. -/
theorem exists_nativeULowerAdjointZero_lower_uniform_mass
    (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    ∃ C_J : ℝ, 0 < C_J ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      HasCoreScalarExpansionBound hO hD
        (fun ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex =>
          lowerCoreAngularGenerator hO hD hF (Prod.fst ij) * lowerCoreAngularGenerator hO hD hF (Prod.snd ij))
        (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) x (C_J*eta) := by
  let K : Set R3 := closedBall y0 rho
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨CC,hCC,hC⟩ := exists_nativeCQuadraticExpansionMass_uniform_smallness hO hD g g2 hg hg2 L hL K hK
  obtain ⟨CW,hCW,hW⟩ := exists_nativeWPolynomialPartMass_uniform_smallness hO hD g g2 hg hg2 L hL K hK
  obtain ⟨CA,hCA,hA⟩ := exists_nativeWeightedYAngularPartMass_uniform_smallness g g2 hg hg2 L hL K hK
  obtain ⟨CS,hCS,hS⟩ := exists_nativeWeightedYScalarCoefficient_uniform_coordinate_word_smallness
    g g2 hg hg2 L hL y0 rho
  obtain ⟨CD,hCD,hDcap⟩ := exists_normalizedSecondDriftDensityDivergence_uniform_coordinate_word_smallness
    g g2 hg hg2 L hL K hK 0
  let C_J : ℝ := 1+CC+CW+CA+CS+CD
  have hCJ : 0 < C_J := by dsimp only [C_J]; positivity
  refine ⟨C_J,hCJ,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  have hbpos : 0 < beta := zero_lt_one.trans_le hb
  have hCCap := hC q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  have hWCap := hW q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  have hACap := hA q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  have hSCap : |nativeWeightedYScalarCoefficient g g2 L q dr Ar p x| ≤ CS*eta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hS q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hs [] (by simp)
  have hD0 : |normalizedSecondDriftDensityDivergence g g2 L q dr Ar p x| ≤ CD*eta/beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,Real.norm_eq_abs,
      beta,actualReferenceBeta] using
      hDcap q hq dr hdr hdr1 Ar hAr p hp eta heta x hx hb hs [] (by simp)
  have hDCap : |normalizedSecondDriftDensityDivergence g g2 L q dr Ar p x| ≤ CD*eta := by
    have hRate : eta/beta ≤ eta := (div_le_iff₀ hbpos).2
      (le_mul_of_one_le_right heta hb)
    calc
      _ ≤ CD*eta/beta := hD0
      _ = CD*(eta/beta) := by ring
      _ ≤ CD*eta := mul_le_mul_of_nonneg_left hRate hCD.le
  have hMass : nativeULowerAdjointZeroLowerMass g g2 L q dr Ar p x ≤ C_J*eta := by
    have hBudget := nativeULowerAdjointZeroLowerMass_le_original_budget g g2 L q dr Ar p x
    dsimp only [C_J]
    nlinarith
  exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (hasCoreScalarExpansionBound_nativeULowerAdjointZero_lower hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr x) hMass

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
