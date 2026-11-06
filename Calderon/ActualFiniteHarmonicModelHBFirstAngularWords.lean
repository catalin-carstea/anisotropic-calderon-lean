import Calderon.ActualFirstAngularCommutatorWordCollection
import Calderon.ActualFiniteHarmonicModelHAngularCommutators

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ActualNormalizedSecondModelErrorAssembly
  AmbientReferenceCovariantCore SmoothMetricFrame MovingFrameConnection ActualAngularCoefficientCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
theorem nativeH_nativeB_commutator_eq_first_angular_words
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l i : Fin 3) :
    let m : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a j =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
            (fun k t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam k t) a j)
    let f : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      m a l+(2 : ℝ) • nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
    let d : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun j =>
      coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
        (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)
    let k : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun j c =>
      coreScalar hO hD (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c)
        (contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c)
    let Gamma : Fin 3 → Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun c b a =>
      coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g1 L lam x
        (referenceMetricGramFrame g1 L (lam,x) c) b a)
        (contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
            (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a)
    ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR) =
    -(∑ a : Fin 3, d i*f a*(coreDerivative hO hD hF a-coreRaising hO hD hF a)) +
      (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        k i c*f a*Gamma c b a*(coreDerivative hO hD hF b+coreRaising hO hD hF b)) -
      (∑ b : Fin 3, m b i*((2 : ℝ) • d l)*coreRaising hO hD hF b) -
      ∑ b : Fin 3, ∑ a : Fin 3, m b i*f a*
        ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
  dsimp only
  let V := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let B := nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
  let N := coreDegree hO hD
  let A (c : Fin 3) := nativeReferenceConnectionAction hO hD g1 hg1 L lam c
  let Rop (b : Fin 3) := coreRaising hO hD hF b
  let sig := coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p i)
    (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR i)
  let m : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a j =>
    coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
      (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
        (fun k t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam k t) a j)
  let f (a : Fin 3) := m a l+(2 : ℝ) • nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
  let d : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun j =>
    coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)
  let k : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun j c =>
    coreScalar hO hD (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c)
      (contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c)
  let Gamma : Fin 3 → Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun c b a =>
    coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g1 L lam x
      (referenceMetricGramFrame g1 L (lam,x) c) b a)
      (contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
        (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a)
  have hB : B=sig+d i*N+(∑ c : Fin 3, k i c*A c)+(∑ b : Fin 3, m b i*Rop b) :=
    nativeB_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i
  have hVC : ScalarCentral hO hD V := nativeH_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  have hVs : Commute V sig := hVC _ _
  have hVd : Commute V (d i) := hVC _ _
  have hVk (c : Fin 3) : Commute V (k i c) := hVC _ _
  have hVm (b : Fin 3) : Commute V (m b i) := hVC _ _
  have hgen := ActualAngularCoefficientCommutator.firstAngularCoefficient_commutator_right
    V sig (d i) N (k i) (fun b => m b i) A Rop hVs hVd hVk hVm
  rw [← hB] at hgen
  have hN : ActualModelCommutatorWords.commutator V N =
      -(∑ a : Fin 3, f a*(coreDerivative hO hD hF a-coreRaising hO hD hF a)) :=
    nativeH_degree_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  have hA (c : Fin 3) : ActualModelCommutatorWords.commutator V (A c) =
      ∑ a : Fin 3, ∑ b : Fin 3, f a*Gamma c b a*(coreDerivative hO hD hF b+coreRaising hO hD hF b) :=
    nativeH_connection_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l c
  have hVraising (b : Fin 3) : ActualModelCommutatorWords.commutator V (Rop b) =
      -((2 : ℝ) • d l)*Rop b - ∑ a : Fin 3, f a*
        ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) :=
    nativeH_raising_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l b
  simp only [hN,hA,hVraising] at hgen
  have hcollect := ActualFirstAngularCommutatorWordCollection.core_firstAngular_commutator_four_block_collection
    hO hD (d i) ((2 : ℝ) • d l) f (fun b => m b i) (k i)
    (fun a => coreDerivative hO hD hF a-coreRaising hO hD hF a)
    (fun b => coreDerivative hO hD hF b+coreRaising hO hD hF b) Rop Gamma
    (fun a b => ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b))
  exact hgen.trans hcollect

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
