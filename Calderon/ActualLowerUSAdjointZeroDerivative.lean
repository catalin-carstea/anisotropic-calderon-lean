import Calderon.ActualLowerUSAdjointCoefficients
import Calderon.ActualFiniteHarmonicModelCHalfForms
import Calderon.ActualFiniteHarmonicModelSecondAngularBounds
import Calderon.ActualFiniteCoreSobolevLift
import Calderon.SphereSobolevBesselOrderCompatibility

/-!
Author: delegated GPT-6.1 Sol, 3 November 2026.
Before-code expansion: ../zero-derivative-upfront.md.
Exact bounded Sobolev representative of the original lower-adjoint zero
coefficient derivative. All profile caps are internally produced. No assertion
that a full physical S output belongs to the finite angular core is made.
Authored only; Root owns compilation and native checking.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualNormalizedPrincipalDensityCoefficientJets ActualMixedDensityScalarZeroForm
  NormalizedPrincipalMetric ReferenceDensityBounds ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint PrincipalCommutator ConformalDepth
  SectionFiveErrorForms ActualReferenceDDSpectralTransport BoundedAngularShift

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- Canonical Bessel/zero-space transport of an actual balanced L2 coefficient. -/
private def lowerZeroBalancedSobolev (A : SphereL2 →L[ℝ] SphereL2) : Hi →L[ℝ] Neg :=
  (sphereSobolevBesselOrderL 0 (-(1/2 : ℝ))).comp
    ((sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A.comp ((sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (sphereSobolevBesselOrderL (3/2 : ℝ) 0))))

private lemma norm_lowerZeroBalancedSobolev_le (A : SphereL2 →L[ℝ] SphereL2) :
    ‖lowerZeroBalancedSobolev hO hD A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  change ‖sphereSobolevZeroEquiv hO hD
    (A ((sphereSobolevZeroEquiv hO hD).symm u))‖ ≤ ‖A‖*‖u‖
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    A.le_opNorm ((sphereSobolevZeroEquiv hO hD).symm u)

private lemma lowerZeroBalancedSobolev_finite_pairing
    (A : SphereL2 →L[ℝ] SphereL2)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    sphereSobolevDualPairing (1/2 : ℝ)
      (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x)
      (lowerZeroBalancedSobolev hO hD A
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
    ⟪A ((coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x),
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G).val x⟫_ℝ := by
  change ⟪sphereSobolevZeroEquiv hO hD
      ((coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G).val x),
    sphereSobolevZeroEquiv hO hD
      (A ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevZeroEquiv hO hD
          ((coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x))))⟫_ℝ = _
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map, real_inner_comm]

private lemma inverseBesselSquare_balanced_pairing
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪F.val x,G.val x⟫_ℝ =
      ⟪((inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD))
        ((coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x),
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G).val x⟫_ℝ := by
  let I := inverseDegreeMultiplier hO hD
  have hI := preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD
  have hII := preservesSphereSpectralGraphs_comp hO hD I I hI hI
  have hFG : (G.val x,(coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G).val x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) :=
    coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hF32 : ((coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x,
      (coreWeightOperator hO hD (besselWeight 2) F).val x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 2) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x) k,
      smul_smul, ← besselWeight_add]
    norm_num
  have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) _ _ _ _
    (hII _ _ _ hF32) hFG
  simpa only [ContinuousLinearMap.comp_apply,I,
    inverseDegreeMultiplier_coreWeight_two_apply,
    inverseDegreeMultiplier_coreWeight_one_apply] using ht

private lemma lowerZeroDerivative_add_sub {R : Type*} [Ring R] (d c w s : R) :
    d*(c+w-s)-(c+w-s)*d = (d*c-c*d)+(d*w-w*d)-(d*s-s*d) := by
  noncomm_ring

variable (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ)
  (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "BC" => nativeCSecondBalancedAngularCoefficient hO hD hF g g2 hg L q dr Ar p
local notation "BW" => nativeWSecondBalancedAngularCoefficient hO hD hF g g2 hg L q dr Ar p
local notation "I2" => ContinuousLinearMap.comp
  (inverseDegreeMultiplier hO hD) (inverseDegreeMultiplier hO hD)
local notation "hRef" => referenceNormalizedPrincipalDifference g g2 L q
local notation "mu" => (fun x => referenceDensityFamily g L (q,x))
local notation "aa" => actualPrincipalMatrix g L q dr Ar p hRef
local notation "a0" => (fun x => adjointZeroCoefficient coordinateDirection mu aa x)
local notation "J" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

/-- Original balanced zero coefficient: both inverse Bessel factors are retained. -/
def nativeULowerAdjointZeroBalanced (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  BC x + BW x - a0 x • I2

/-- Literal first derivative of the three original balanced coefficient rows. -/
def nativeULowerAdjointZeroDerivativeBalanced (i : Fin 3) (x : R3) :
    SphereL2 →L[ℝ] SphereL2 :=
  directionalFDeriv (coordinateDirection i) BC x +
    directionalFDeriv (coordinateDirection i) BW x -
    directionalFDeriv (coordinateDirection i) a0 x • I2

/-- Actual bounded Hi-to-negative-half representative of the lower zero derivative. -/
def nativeULowerAdjointZeroDerivativeSobolev (i : Fin 3) (x : R3) : Hi →L[ℝ] Neg :=
  lowerZeroBalancedSobolev hO hD
    (nativeULowerAdjointZeroDerivativeBalanced hO hD hF g g2 hg L q dr Ar p i x)

local notation "BJd" => nativeULowerAdjointZeroDerivativeBalanced hO hD hF g g2 hg L q dr Ar p
local notation "JSd" => nativeULowerAdjointZeroDerivativeSobolev hO hD hF g g2 hg L q dr Ar p

/-- Finite-input graph identifies the bounded representative with the EXACT
original native zero derivative. It imposes no finite-output condition on S. -/
theorem nativeULowerAdjointZeroDerivativeSobolev_finite_graph
    (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    sphereSobolevDualPairing (1/2 : ℝ)
      (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x)
      (JSd i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
    ⟪(coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) J F).val x,
      G.val x⟫_ℝ := by
  rw [nativeULowerAdjointZeroDerivativeSobolev, lowerZeroBalancedSobolev_finite_pairing]
  have ha : ContDiff ℝ ∞ a0 :=
    contDiff_modelAdjointZeroCoefficient g g2 hg hg2 L q dr Ar p hdr hAr
  let C0 := nativeC hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
  let W0 := nativeW hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
  let S0 := coreScalar hO hD a0 ha
  let d := coreDirectionalDerivative hO hD (coordinateDirection i)
  have hSplit : coefficientDerivative d J =
      coefficientDerivative d C0 + coefficientDerivative d W0 - coefficientDerivative d S0 := by
    rw [nativeULowerAdjointZeroCoefficient_eq_original hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr]
    dsimp only [C0,W0,S0]
    change d*(C0+W0-S0) - (C0+W0-S0)*d =
      (d*C0-C0*d)+(d*W0-W0*d)-(d*S0-S0*d)
    exact lowerZeroDerivative_add_sub d C0 W0 S0
  rw [hSplit]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Submodule.coe_sub, Submodule.coe_add,
    Pi.sub_apply, Pi.add_apply, inner_sub_left, inner_add_left]
  rw [coefficientDerivative_nativeC_secondAngular_inner_threehalf_half hO hD hF g g2 hg
      L q dr Ar p hg2 hdr hAr i F G x,
    coefficientDerivative_nativeW_secondAngular_inner_threehalf_half hO hD hF g g2 hg
      L q dr Ar p hg2 hdr hAr i F G x]
  have hScalar : ⟪(coefficientDerivative d S0 F).val x,G.val x⟫_ℝ =
      directionalFDeriv (coordinateDirection i) a0 x *
        ⟪I2 ((coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x),
          (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G).val x⟫_ℝ := by
    dsimp only [d,S0]
    rw [coefficientDerivative_coreScalar]
    change ⟪directionalFDeriv (coordinateDirection i) a0 x • F.val x,G.val x⟫_ℝ = _
    rw [real_inner_smul_left, inverseBesselSquare_balanced_pairing hO hD F G x]
  rw [hScalar]
  simp only [nativeULowerAdjointZeroDerivativeBalanced, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_sub_left, inner_add_left, real_inner_smul_left]

include hg2 in
/-- All first derivative caps are derived from the selected C/W balanced jets
and actual scalar a0 jets, on the fixed original compact background. -/
theorem exists_nativeULowerAdjointZeroDerivativeSobolev_uniform_bound
    (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    ∃ C_J : ℝ, 0 < C_J ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i : Fin 3,
        ‖nativeULowerAdjointZeroDerivativeSobolev hO hD hF g g2 hg L q dr Ar p i x‖ ≤
          C_J*eta*actualReferenceBeta g L q dr Ar p x := by
  let K : Set R3 := closedBall y0 rho
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨CC,hCC,hC⟩ := exists_nativeCSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g g2 hg hg2 L hL K hK
  obtain ⟨CW,hCW,hW⟩ := exists_nativeWSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g g2 hg hg2 L hL K hK
  obtain ⟨M,hM,hGeom⟩ := exists_mixed_principal_density_background_jet_bound g hg L K hK 3
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g hg L hL K hK 3
  let Ca : ℝ := scalarAdjointZeroCoordinateJetConstant 1*Cr*M^3
  let NI : ℝ := ‖(inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)‖
  let C_J : ℝ := 1+CC+CW+Ca*NI
  have hCa : 0 ≤ Ca := by
    dsimp only [Ca,scalarAdjointZeroCoordinateJetConstant,
      weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]
    positivity
  have hNI : 0 ≤ NI := norm_nonneg _
  have hCJ : 0 < C_J := by dsimp only [C_J]; positivity
  refine ⟨C_J,hCJ,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let r : ℝ := referenceRadius dr Ar p L x
  let scalarZeroField : R3 → ℝ := fun y => adjointZeroCoefficient coordinateDirection
    (fun z => referenceDensityFamily g L (q,z))
    (actualPrincipalMatrix g L q dr Ar p (referenceNormalizedPrincipalDifference g g2 L q)) y
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  change r*beta^2 ≤ eta at hs
  have hr1 : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb (n := 2))).trans hs).trans heta1
  have hetaR : eta*r ≤ 1 :=
    (mul_le_mul_of_nonneg_left hr1 heta).trans (by simpa only [mul_one] using heta1)
  have hAcap := abs_actualScalarAdjointZero_coordinate_word_le g g2 hg hg2 L q dr Ar p x
    eta M Cr 1 (by norm_num) hdr hAr heta hM hCr.le hetaR hb
    (hGeom q hq x hx) (hRadius q hq dr hdr hdr1 Ar hAr p hp x hx) hH8 [i] (by simp)
  have hA : |directionalFDeriv (coordinateDirection i) scalarZeroField x| ≤ Ca*eta*beta := by
    have hRaw : |directionalFDeriv (coordinateDirection i) scalarZeroField x| ≤ Ca*r*beta^3 := by
      simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,
        Ca,r,beta,scalarZeroField] using hAcap
    calc
      _ ≤ Ca*r*beta^3 := hRaw
      _ = Ca*(r*beta^2)*beta := by ring
      _ ≤ Ca*eta*beta := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs hCa) hb0
  have hBC : ‖directionalFDeriv (coordinateDirection i)
      (nativeCSecondBalancedAngularCoefficient hO hD hF g g2 hg L q dr Ar p) x‖ ≤ CC*eta*beta := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one,beta] using
      hC q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs [i] (by simp)
  have hBW : ‖directionalFDeriv (coordinateDirection i)
      (nativeWSecondBalancedAngularCoefficient hO hD hF g g2 hg L q dr Ar p) x‖ ≤ CW*eta*beta := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one,beta] using
      hW q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs [i] (by simp)
  have hScalar : ‖directionalFDeriv (coordinateDirection i) scalarZeroField x •
      ((inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD))‖ ≤ Ca*eta*beta*NI := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hA hNI
  calc
    _ ≤ ‖nativeULowerAdjointZeroDerivativeBalanced hO hD hF g g2 hg L q dr Ar p i x‖ :=
      norm_lowerZeroBalancedSobolev_le hO hD _
    _ ≤ CC*eta*beta+CW*eta*beta+Ca*eta*beta*NI := by
      unfold nativeULowerAdjointZeroDerivativeBalanced
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hBC hBW)) hScalar)
    _ ≤ C_J*eta*beta := by
      dsimp only [C_J]
      nlinarith [mul_nonneg heta hb0]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
