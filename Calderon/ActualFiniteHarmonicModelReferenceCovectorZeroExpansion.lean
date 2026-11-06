import Calderon.ActualFiniteHarmonicModelConnectionDerivativeExpansion

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection AmbientReferenceCovariantCore
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeReferenceWeightedZeroRawMass (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3) (x : R3) : ℝ :=
  nativeReferenceConnectionCoefficientMass g L lam a x+
    |referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x|

lemma hasCoreScalarExpansionBound_nativeReferenceWeightedZeroRaw
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeReferenceConnectionAction hO hD g hg L lam a+
        nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*coreDegree hO hD) x
      (nativeReferenceWeightedZeroRawMass g L lam δ R p a x) := by
  apply hasCoreScalarExpansionBound_add hO hD
  · exact hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g hg L lam a x
  · have ht := hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
      (Sum.inr (Sum.inr (Sum.inr true)))
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      (contDiff_referenceFrameDerivative g hg L lam a _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)) x
    exact ht

def nativeReferenceCovectorZeroRawMass (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3) (x : R3) : ℝ :=
  let q (c : Fin 3) := referenceFrameDerivative g L lam c (fun y => Real.log (referenceRadius δ R p L y))
  nativeReferenceConnectionDerivativeMass g L lam a b x+
    |referenceFrameDerivative g L lam a (q b) x|+
    nativeReferenceConnectionCoefficientMass g L lam a x*nativeReferenceWeightedZeroRawMass g L lam δ R p b x+
    (∑ c : Fin 3, |referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) c b| *
      nativeReferenceWeightedZeroRawMass g L lam δ R p c x)+
    |q a x| *nativeReferenceWeightedZeroRawMass g L lam δ R p b x

lemma hasCoreScalarExpansionBound_nativeReferenceCovectorZeroRawAction
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a b : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeReferenceCovectorZeroRawAction hO hD g hg L lam δ R p hδ hR a b) x
      (nativeReferenceCovectorZeroRawMass g L lam δ R p a b x) := by
  let G := coreAngularGenerator hO hD hF
  let Q := fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex => G ij.1*G ij.2
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
    hasCoreScalarExpansionBound_nativeReferenceWeightedZeroRaw hO hD hF g hg L lam δ R p hδ hR c x
  have hdA := hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF _ x _
    (hasCoreScalarExpansionBound_nativeReferenceConnectionFrameDerivative hO hD hF g hg L lam a b x)
  have hdP : HasCoreScalarExpansionBound hO hD Q
      (nativeReferenceProfileFrameDerivative hO hD g hg L lam δ R p hδ hR a b*coreDegree hO hD) x
      |referenceFrameDerivative g L lam a (q b) x| := by
    apply hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF
    exact hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inr (Sum.inr true)))
      (referenceFrameDerivative g L lam a (q b))
      (contDiff_referenceFrameDerivative g hg L lam a _ (hq b)) x
  have hprod := hasCoreScalarExpansionBound_product hO hD G G
    (scalarCentral_coreAngularGenerator hO hD hF) (A a) (Z b) x _ _
    (hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g hg L lam a x) (hz b)
  have hsum : HasCoreScalarExpansionBound hO hD Q
      (∑ c : Fin 3, coreScalar hO hD (gamma c) (hgamm c)*Z c) x
      (∑ c : Fin 3, |gamma c x| *M c) := by
    apply hasCoreScalarExpansionBound_linear_to_quadratic hO hD hF
    apply hasCoreScalarExpansionBound_sum hO hD
    intro c _
    exact hasCoreScalarExpansionBound_scalar_mul hO hD G (Z c) x (M c) (hz c) (gamma c) (hgamm c)
  have hpz : HasCoreScalarExpansionBound hO hD G (P a*Z b) x (|q a x| *M b) :=
    hasCoreScalarExpansionBound_scalar_mul hO hD G (Z b) x (M b) (hz b) (q a) (hq a)
  have hlast : HasCoreScalarExpansionBound hO hD Q ((P a*Z b)*coreDegree hO hD) x (|q a x| *M b) := by
    have hn := hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inr true))) x
    simpa only [mul_one] using hasCoreScalarExpansionBound_product hO hD G G
      (scalarCentral_coreAngularGenerator hO hD hF) (P a*Z b) (coreDegree hO hD) x _ 1 hpz hn
  exact hasCoreScalarExpansionBound_add hO hD Q _ _ x _ _
    (hasCoreScalarExpansionBound_sub hO hD Q _ _ x _ _
      (hasCoreScalarExpansionBound_add hO hD Q _ _ x _ _
        (hasCoreScalarExpansionBound_add hO hD Q _ _ x _ _ hdA hdP) hprod) hsum) hlast

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
