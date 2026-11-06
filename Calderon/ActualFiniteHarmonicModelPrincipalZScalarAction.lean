import Calderon.ActualFiniteHarmonicModelUZSecondBaseAdjointRegularity

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  PrincipalCommutator AmbientReferenceRaising ConformalDepth SmoothMetricFrame MovingFrameConnection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativePrincipalZScalarFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativePrincipalZScalarFunction

def nativePrincipalDefectScalarCoefficient
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (i j a : Fin 3) : R3 → ℝ :=
  fun x => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) x i j *
    referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x

lemma contDiff_nativePrincipalDefectScalarCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j a : Fin 3) :
    ContDiff ℝ ∞ (nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a) := by
  exact (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g1 hg1
    L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) hδ hR
    (fun b c => contDiff_referenceNormalizedPrincipalDifference_entry
      g1 g2 hg1 hg2 L lam b c) i j).mul
    (contDiff_referenceFrameDerivative g1 hg1 L lam a _
      (ConformalDepth.contDiff_log_referenceRadius_profile δ R L p hδ hR))

lemma nativePrincipalCoefficient_nativeZ_scalar_angular_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x =
      ∑ a : Fin 3, nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x •
        coreDerivative hO hD hF a F x := by
  rw [nativePrincipalCoefficient_nativeZ_firstAngular_apply]
  simp only [nativePrincipalZFirstAngularCoefficient,
    nativeReferenceDefectFirstNormalizedCoefficient, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, Finset.smul_sum, smul_smul,
    nativePrincipalDefectScalarCoefficient, coreDerivative, Module.End.mul_apply,
    coreNormalizedDerivative, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk]

lemma coreDirectionalDerivative_coreDerivative_commute
    (hF : SphereFischerInner) (v : R3) (a : Fin 3) :
    Commute (coreDirectionalDerivative hO hD v) (coreDerivative hO hD hF a) := by
  unfold coreDerivative
  exact (coreDirectionalDerivative_normalizedDerivative_commute hO hD v hF a).mul_right
    (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).symm

lemma coreDerivative_secondBaseDerivative_apply
    (hF : SphereFischerInner) (a : Fin 3) (i j : R3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreDerivative hO hD hF a
      (coreDirectionalDerivative hO hD i (coreDirectionalDerivative hO hD j F)) x =
      BaseDensityAdjoint.directionalDeriv i (BaseDensityAdjoint.directionalDeriv j
        (coreDerivative hO hD hF a F : R3 → SphereL2)) x := by
  have hi := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
      T (coreDirectionalDerivative hO hD j F))
    (coreDirectionalDerivative_coreDerivative_commute hO hD hF i a).symm.eq
  have hj := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F)
    (coreDirectionalDerivative_coreDerivative_commute hO hD hF j a).symm.eq
  change coreDerivative hO hD hF a
      (coreDirectionalDerivative hO hD i (coreDirectionalDerivative hO hD j F)) =
    coreDirectionalDerivative hO hD i
      (coreDerivative hO hD hF a (coreDirectionalDerivative hO hD j F)) at hi
  change coreDerivative hO hD hF a (coreDirectionalDerivative hO hD j F) =
    coreDirectionalDerivative hO hD j (coreDerivative hO hD hF a F) at hj
  rw [hj] at hi
  exact congrArg (fun G : smoothCompactFiniteSphereCore hO hD => G x) hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
