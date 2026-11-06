import Calderon.ActualFiniteHarmonicModelAngularBaseCommutation
import Calderon.ActualFiniteHarmonicModelReferenceZeroExpansions

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
  SmoothMetricFrame AmbientReferenceRaising AmbientReferenceCovariantCore
  ConformalDepth MovingFrameConnection PrincipalCommutator ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeReferenceZeroDerivativeExpansionMass
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (v : R3) (x : R3) : ℝ :=
  ∑ a : Fin 3, ((1/2 : ℝ)*(∑ b : Fin 3, ∑ c : Fin 3,
    |directionalFDeriv v (fun y => referenceFrameConnectionCoefficient g L lam y
      (referenceMetricGramFrame g L (lam,y) a) b c) x|) +
    |directionalFDeriv v (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))) x|)

lemma coefficientDerivative_coreEnd_smul
    (d A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (t : ℝ) :
    coefficientDerivative d (t • A) = t • coefficientDerivative d A := by
  unfold coefficientDerivative ActualModelCommutatorWords.commutator
  rw [mul_smul_comm,smul_mul_assoc,smul_sub]

lemma hasCoreScalarExpansionBound_nativeReferenceConnection_derivative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : Fin 3) (v : R3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (coefficientDerivative (coreDirectionalDerivative hO hD v)
        (nativeReferenceConnectionAction hO hD g hg L lam a)) x
      ((1/2 : ℝ)*(∑ b : Fin 3, ∑ c : Fin 3,
        |directionalFDeriv v (fun y => referenceFrameConnectionCoefficient g L lam y
          (referenceMetricGramFrame g L (lam,y) a) b c) x|)) := by
  let G := coreAngularGenerator hO hD hF
  let gamma (b c : Fin 3) (y : R3) := referenceFrameConnectionCoefficient g L lam y
    (referenceMetricGramFrame g L (lam,y) a) b c
  have hgamma (b c : Fin 3) : ContDiff ℝ ∞ (gamma b c) := contDiff_referenceFrameConnectionCoefficient_field
    g hg L lam _ (contDiff_referenceMetricGramFrame_slice g hg L lam a) b c
  have hword (b c : Fin 3) : HasCoreScalarExpansionBound hO hD G
      (coefficientDerivative (coreDirectionalDerivative hO hD v)
        (coreScalar hO hD (gamma b c) (hgamma b c)*coreRotation hO hD b c)) x
      |directionalFDeriv v (gamma b c) x| := by
    have hcomm := coreDirectionalDerivative_coreAngularGenerator_commute hO hD hF v
      (Sum.inr (Sum.inr (Sum.inl (b,c))))
    have hz : coefficientDerivative (coreDirectionalDerivative hO hD v) (coreRotation hO hD b c) = 0 := sub_eq_zero.mpr hcomm.eq
    rw [coefficientDerivative_coreScalar_mul,hz,mul_zero,add_zero]
    exact hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inr (Sum.inl (b,c)))) _ _ x
  have hsum := hasCoreScalarExpansionBound_sum hO hD G Finset.univ
    (fun b => ∑ c : Fin 3, coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coreScalar hO hD (gamma b c) (hgamma b c)*coreRotation hO hD b c)) x
    (fun b => ∑ c : Fin 3, |directionalFDeriv v (gamma b c) x|)
    (fun b _ => hasCoreScalarExpansionBound_sum hO hD G Finset.univ _ x _ (fun c _ => hword b c))
  have ht := hasCoreScalarExpansionBound_smul hO hD G _ x _ (1/2 : ℝ) hsum
  unfold nativeReferenceConnectionAction
  rw [coefficientDerivative_coreEnd_smul]
  unfold coefficientDerivative
  simp only [ActualModelCommutatorWords.commutator_sum_right]
  simpa only [G,gamma,coefficientDerivative,abs_of_pos (by norm_num : 0 < (1/2 : ℝ))] using ht

lemma hasCoreScalarExpansionBound_nativeReferenceZero_derivative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (v : R3) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (coefficientDerivative (coreDirectionalDerivative hO hD v)
        (nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) x
      (nativeReferenceZeroDerivativeExpansionMass g L lam δ R p v x) := by
  let G := coreAngularGenerator hO hD hF
  let d := coreDirectionalDerivative hO hD v
  let q (a : Fin 3) := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hq (a : Fin 3) : ContDiff ℝ ∞ (q a) := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hprod {S : Type} [Ring S] (d A B : S) : coefficientDerivative d (A*B)=
      coefficientDerivative d A*B+A*coefficientDerivative d B := by
    unfold coefficientDerivative ActualModelCommutatorWords.commutator
    noncomm_ring
  have hadd {S : Type} [Ring S] (d A B : S) : coefficientDerivative d (A+B)=
      coefficientDerivative d A+coefficientDerivative d B := by
    unfold coefficientDerivative ActualModelCommutatorWords.commutator
    noncomm_ring
  unfold nativeReferenceZeroCoefficient nativeReferenceZeroDerivativeExpansionMass
  rw [coefficientDerivative,ActualModelCommutatorWords.commutator_sum_right]
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  have hRA := coreDirectionalDerivative_coreAngularGenerator_commute hO hD hF v (Sum.inr (Sum.inl a))
  have hN := coreDirectionalDerivative_coreAngularGenerator_commute hO hD hF v (Sum.inr (Sum.inr (Sum.inr true)))
  have hzRA : coefficientDerivative d (coreRaising hO hD hF a) = 0 := sub_eq_zero.mpr hRA.eq
  have hzN : coefficientDerivative d (coreDegree hO hD) = 0 := sub_eq_zero.mpr hN.eq
  change HasCoreScalarExpansionBound hO hD (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex => G ij.1*G ij.2)
    (coefficientDerivative d (coreRaising hO hD hF a*(nativeReferenceConnectionAction hO hD g hg L lam a+
      nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*coreDegree hO hD))) x _
  rw [hprod,hzRA,zero_mul,zero_add,hadd,hprod,hzN,mul_zero,add_zero]
  have hc := hasCoreScalarExpansionBound_nativeReferenceConnection_derivative hO hD hF g hg L lam a v x
  have hp : HasCoreScalarExpansionBound hO hD G
      (coefficientDerivative d (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a)*coreDegree hO hD) x
      |directionalFDeriv v (q a) x| := by
    unfold nativeReferenceProfileScalar
    rw [coefficientDerivative_coreScalar]
    exact hasCoreScalarExpansionBound_single hO hD G (Sum.inr (Sum.inr (Sum.inr true))) _ _ x
  have hi := hasCoreScalarExpansionBound_add hO hD G _ _ x _ _ hc hp
  have hRAexp : HasCoreScalarExpansionBound hO hD G (coreRaising hO hD hF a) x 1 :=
    hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inl a)) x
  simpa only [one_mul,q] using hasCoreScalarExpansionBound_product hO hD G G
    (scalarCentral_coreAngularGenerator hO hD hF) _ _ x 1 _ hRAexp hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
