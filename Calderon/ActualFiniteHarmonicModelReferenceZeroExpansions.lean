import Calderon.ActualFiniteHarmonicModelReferenceConnectionExpansion

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma hasCoreScalarExpansionBound_nativeReferenceZeroCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR) x
      (∑ a : Fin 3, (nativeReferenceConnectionCoefficientMass g L lam a x+
        |referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x|)) := by
  let GG := coreAngularGenerator hO hD hF
  let q (a : Fin 3) := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hq (a : Fin 3) : ContDiff ℝ ∞ (q a) :=
    contDiff_referenceFrameDerivative g hg L lam a _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hconn (a : Fin 3) := hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g hg L lam a x
  have hn : HasCoreScalarExpansionBound hO hD GG (coreDegree hO hD) x 1 :=
    hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inr true))) x
  have hp (a : Fin 3) : HasCoreScalarExpansionBound hO hD GG
      (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*coreDegree hO hD) x (|q a x|) := by
    have ht := hasCoreScalarExpansionBound_scalar_mul hO hD GG (coreDegree hO hD) x 1
      hn (q a) (hq a)
    change HasCoreScalarExpansionBound hO hD GG
      (coreScalar hO hD (q a) (hq a)*coreDegree hO hD) x |q a x|
    simpa only [mul_one] using ht
  have hin (a : Fin 3) := hasCoreScalarExpansionBound_add hO hD GG
    (nativeReferenceConnectionAction hO hD g hg L lam a)
    (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*coreDegree hO hD) x
    (nativeReferenceConnectionCoefficientMass g L lam a x) (|q a x|)
    (hconn a) (hp a)
  have hout (a : Fin 3) : HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex => GG ij.1*GG ij.2)
      (coreRaising hO hD hF a*(nativeReferenceConnectionAction hO hD g hg L lam a+
        nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*coreDegree hO hD)) x
      (nativeReferenceConnectionCoefficientMass g L lam a x+|q a x|) := by
    have hd : HasCoreScalarExpansionBound hO hD GG (coreRaising hO hD hF a) x 1 :=
      hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inl a)) x
    simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD GG GG
      (scalarCentral_coreAngularGenerator hO hD hF) _ _ x 1 _ hd (hin a)
  unfold nativeReferenceZeroCoefficient
  exact hasCoreScalarExpansionBound_sum hO hD _ Finset.univ _ x _ (fun a _ => hout a)

lemma hasCoreScalarExpansionBound_nativeReferenceAdjointZeroCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR) x
      (∑ a : Fin 3, (nativeReferenceConnectionCoefficientMass g L lam a x+
        2*|referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x|)) := by
  let GG := coreAngularGenerator hO hD hF
  let q (a : Fin 3) := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hq (a : Fin 3) : ContDiff ℝ ∞ (q a) :=
    contDiff_referenceFrameDerivative g hg L lam a _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hconn (a : Fin 3) := hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g hg L lam a x
  have hn : HasCoreScalarExpansionBound hO hD GG (coreDegree hO hD) x 1 :=
    hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inr true))) x
  have hni := hasCoreScalarExpansionBound_sub hO hD GG (coreDegree hO hD) 1 x 1 1 hn
    (hasCoreScalarExpansionBound_identity hO hD hF x)
  have hp (a : Fin 3) : HasCoreScalarExpansionBound hO hD GG
      (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*(coreDegree hO hD-1)) x (2*|q a x|) := by
    have ht := hasCoreScalarExpansionBound_scalar_mul hO hD GG (coreDegree hO hD-1) x (1+1)
      hni (q a) (hq a)
    change HasCoreScalarExpansionBound hO hD GG
      (coreScalar hO hD (q a) (hq a)*(coreDegree hO hD-1)) x (2*|q a x|)
    convert ht using 1 <;> ring
  have hin (a : Fin 3) := hasCoreScalarExpansionBound_add hO hD GG
    (-nativeReferenceConnectionAction hO hD g hg L lam a)
    (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*(coreDegree hO hD-1)) x
    (nativeReferenceConnectionCoefficientMass g L lam a x) (2*|q a x|)
    (hasCoreScalarExpansionBound_neg hO hD GG _ x _ (hconn a)) (hp a)
  have hout (a : Fin 3) : HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex => GG ij.1*GG ij.2)
      (coreDerivative hO hD hF a*(-nativeReferenceConnectionAction hO hD g hg L lam a+
        nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*(coreDegree hO hD-1))) x
      (nativeReferenceConnectionCoefficientMass g L lam a x+2*|q a x|) := by
    have hd : HasCoreScalarExpansionBound hO hD GG (coreDerivative hO hD hF a) x 1 :=
      hasCoreScalarExpansionBound_generator hO hD hF (Sum.inl a) x
    simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD GG GG
      (scalarCentral_coreAngularGenerator hO hD hF) _ _ x 1 _ hd (hin a)
  rw [nativeReferenceAdjointZeroCoefficient_eq_raw hO hD hF g hg L lam δ R p hδ hR]
  exact hasCoreScalarExpansionBound_sum hO hD _ Finset.univ _ x _ (fun a _ => hout a)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
