import Calderon.ActualFiniteHarmonicModelGeneratorScalarExpansions
import Calderon.ActualFiniteHarmonicModelReferenceAdjointZeroRaw

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeReferenceConnectionCoefficientMass (g : MatrixField) (L lam : ℝ) (a : Fin 3) (x : R3) : ℝ :=
  (1/2 : ℝ)*(∑ b : Fin 3, ∑ c : Fin 3,
    |referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) b c|)

lemma hasCoreScalarExpansionBound_nativeReferenceConnectionAction
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeReferenceConnectionAction hO hD g hg L lam a) x
      (nativeReferenceConnectionCoefficientMass g L lam a x) := by
  let G := coreAngularGenerator hO hD hF
  let c (b d : Fin 3) (y : R3) := referenceFrameConnectionCoefficient g L lam y
    (referenceMetricGramFrame g L (lam,y) a) b d
  have hc (b d : Fin 3) : ContDiff ℝ ∞ (c b d) :=
    AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field
      g hg L lam _ (contDiff_referenceMetricGramFrame_slice g hg L lam a) b d
  have he (b d : Fin 3) : HasCoreScalarExpansionBound hO hD G
      (coreScalar hO hD (c b d) (hc b d)*coreRotation hO hD b d) x |c b d x| :=
    hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inr (Sum.inl (b,d))))
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

lemma hasCoreScalarExpansionBound_nativeReferenceProfileScalar
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a) x
      |referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x| := by
  exact hasCoreScalarExpansionBound_coreScalar hO hD hF _ _ x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
