import Calderon.ActualMovingAdjointPiDecomposition
import Calderon.ActualNativeZeroCoordinateCovariantTransport
import Calderon.ActualAngularPiMixedLowInstantiationDraft
import Calderon.ActualJacobiCommonSupportMultiplierGerms
import Calderon.ActualFirstCorrectionParameterJets
import Calderon.ActualFirstCorrectionSobolevFamilies

/-! Sol author candidate. Full upfront: before-source-v001/MATHEMATICS.md §§1–3.
No check or independent review is claimed. The forward coefficient is the literal
moving E; the reverse below is the ordered angular reverse, not the raw lower E. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedEndpoints
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  ActualAngularHighDraft ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete


section OrderedZeroAlgebra
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
private lemma orderedZeroReverse_graph
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (EH : X →L[ℝ] Y) (EL : Y →L[ℝ] Z)
    (zH : X →L[ℝ] X) (zL : Y →L[ℝ] Y) (zN : Z →L[ℝ] Z)
    (hE : ∀ u, J (EH u)=EL (I u))
    (hZ : ∀ v, J (zL v)=zN (J v)) (hH : ∀ u, I (zH u)=zL (I u)) (u : X) :
    J ((zL.comp EH-EH.comp zH) u)=zN (EL (I u))-EL (zL (I u)) := by
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_sub,hZ,hE,hH]
private lemma norm_orderedZeroRow_le (A : Y →L[ℝ] Y) (T : X →L[ℝ] Y) (B : X →L[ℝ] X) :
    ‖A.comp T-T.comp B‖ ≤ ‖A‖*‖T‖+‖T‖*‖B‖ :=
  (norm_sub_le (A.comp T) (T.comp B)).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le A T) (ContinuousLinearMap.opNorm_comp_le T B))
private lemma finiteTriple_compat
    (I : X →L[ℝ] Y) (r : ℝ)
    (AH BH CH : Fin 3 → X →L[ℝ] X) (AL BL CL : Fin 3 → Y →L[ℝ] Y)
    (hA : ∀ j u, I (AH j u)=AL j (I u))
    (hB : ∀ j u, I (BH j u)=BL j (I u))
    (hC : ∀ j u, I (CH j u)=CL j (I u)) (u : X) :
    I ((r • ∑ j : Fin 3,(AH j).comp ((BH j).comp (CH j))) u)=
      (r • ∑ j : Fin 3,(AL j).comp ((BL j).comp (CL j))) (I u) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,map_smul,map_sum,hA,hB,hC]
private lemma finiteFirstOrder_compat
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z)
    (RH : X →L[ℝ] Y) (RL : Y →L[ℝ] Z) (AH : Fin 3 → X →L[ℝ] Y) (AL : Fin 3 → Y →L[ℝ] Z)
    (ZH : X →L[ℝ] X) (ZL : Y →L[ℝ] Y)
    (hR : ∀ u, J (RH u)=RL (I u)) (hA : ∀ j u, J (AH j u)=AL j (I u))
    (hZ : ∀ u, I (ZH u)=ZL (I u)) (u : X) :
    J ((RH+(∑ j : Fin 3,AH j)+I.comp ZH) u)=
      (RL+(∑ j : Fin 3,AL j)+J.comp ZL) (I u) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sum,hR,hA,hZ]
end OrderedZeroAlgebra

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily
  g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily
  g hg L y0 Φ B ε C ρ H a w hData
local notation "NH" i:max j:max p:max => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (NJ3 i j p)
local notation "NL" i:max j:max p:max => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (NJ2 i j p)
local notation "NN" i:max j:max p:max => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (NJ2 i j p)
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
local notation "Dr" s:max p:max => sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L p.1 p.2.1)
local notation "dr" s:max p:max => sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L p.1 p.2.1)

/-- The genuine order-zero H0 word, before inclusion to a first-order endpoint. -/
def zeroCorrectionHigh (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Hi :=
  p.2.2 • ∑ j : Fin 3, (Dr (3/2 : ℝ) p).comp ((Mh j).comp (NH i j p))
def zeroCorrectionHalf (i : Fin 3) (p : Pphys) : Half →L[ℝ] Half :=
  p.2.2 • ∑ j : Fin 3, (Dr (1/2 : ℝ) p).comp ((Ml j).comp (NL i j p))
def zeroCorrectionNegative (i : Fin 3) (p : Pphys) : Neg →L[ℝ] Neg :=
  p.2.2 • ∑ j : Fin 3, (Dr (-(1/2 : ℝ)) p).comp ((Mn j).comp (NN i j p))

/-- Reversal keeps the exact order N M Dsharp. -/
def zeroReverseHigh (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Hi :=
  p.2.2 • ∑ j : Fin 3, (NH i j p).comp ((Mh j).comp (dr (3/2 : ℝ) p))
def zeroReverseHalf (i : Fin 3) (p : Pphys) : Half →L[ℝ] Half :=
  p.2.2 • ∑ j : Fin 3, (NL i j p).comp ((Ml j).comp (dr (1/2 : ℝ) p))
def zeroReverseNegative (i : Fin 3) (p : Pphys) : Neg →L[ℝ] Neg :=
  p.2.2 • ∑ j : Fin 3, (NN i j p).comp ((Mn j).comp (dr (-(1/2 : ℝ)) p))

local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZN" => zeroCorrectionNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zN" => zeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Canonical full E, including every H1 and H0 term. -/
def canonicalHigh (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (Th t.1).comp (PiH i t) +
    (∑ j : Fin 3, (raisingHigh hF hO hD j).comp (NH i j t.1)) + (IH).comp (ZH i t.1)
def canonicalLow (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (Tl t.1).comp (PiL i t) +
    (∑ j : Fin 3, (raisingLow hF hO hD j).comp (NL i j t.1)) + (JL).comp (ZL i t.1)

private def orderedReverseHigh (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (PiL i t).comp (Sh t.1) +
    (∑ j : Fin 3, (NL i j t.1).comp (loweringHigh hF hO hD j)) + (IH).comp (zH i t.1)
private def orderedReverseLow (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (PiN i t).comp (Sl t.1) +
    (∑ j : Fin 3, (NN i j t.1).comp (loweringLow hF hO hD j)) + (JL).comp (zL i t.1)

local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceHighAdjointCoordinateBoundaryFamily referenceAdjointThreeHalfRadialFamily
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevRadialDriftAdjointL sphereSobolevRadialDriftL
  sphereSobolevLinearCoordinateMulL referenceRadialEndpointInvertibleLocus
  sphereSobolevInclusionL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  loweringHigh loweringLow raisingHigh raisingLow
  adjointHighRemainder adjointHalfRemainder sharpRemainder lowerSharpRemainder

/-- Canonicalization uses the local zero-family germ, not a pointwise derivative assumption. -/
theorem zeroCoordinate_germ_eq_raisingHigh
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ < ρ) (j : Fin 3) :
    (fun x : R3 => referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,0)) j) =ᶠ[𝓝 y]
      (fun _ => raisingHigh hF hO hD j) := by
  have h := referenceHighAdjointCoordinateBoundaryFamily_zero_eventually_eq_angularTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy j
  simpa only [sphereSobolevAngularCoordinateTransposeL, raisingHigh] using h

/-- Literal current-profile E equals the canonical full first-order word. -/
theorem movingDifferenceQuotient_eq_canonicalHigh
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hr : R y ≠ 0)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (i : Fin 3) :
    referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i =
      EH i ((q,(y,R y)),fderiv ℝ R y) := by
  have hy' : ‖y-y0‖ ≤ ρ := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hDjet := deriv_referenceAdjointThreeHalfRadialFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy'
  have hA (j : Fin 3) : referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j =
      raisingHigh hF hO hD j := by
    have hj := referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy' j
    simpa only [sphereHighHarmonicDerivativeTransposeL, raisingHigh] using hj
  apply ContinuousLinearMap.ext
  intro u
  have h := referenceHighAdjointMovingDifferenceQuotient_eq_originalPi_radial_add_first_order
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy hr hSegment hInv i u
  simp only [hA, hDjet, ContinuousLinearMap.comp_apply] at h
  change _ = Th (q,(y,R y)) (PiH i ((q,(y,R y)),fderiv ℝ R y) u) +
    (∑ j : Fin 3, raisingHigh hF hO hD j ((NH i j (q,(y,R y))) u)) +
    IH (ZH i (q,(y,R y)) u)
  simpa only [referenceOriginalPiAdjointRadialCoefficient, adjointHighRemainder,
    zeroCorrectionHigh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, map_smul, map_sum] using h

/-- Nine actual Jacobi germ witnesses, before derivative caps and inputs. -/
theorem exists_actualJacobi_native_germs
    (K : Set Pphys) (hK : IsCompact K)
    (hInv : ∀ p ∈ K, ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,ξ.val))).IsInvertible) :
    ∃ (m : Fin 3 → Fin 3 → Pphys × R3 → ℝ)
      (hm : ∀ i j, ContDiff ℝ ∞ (m i j))
      (Km : Fin 3 → Fin 3 → Set R3) (hKm : ∀ i j, IsCompact (Km i j))
      (hmz : ∀ i j p x, x ∉ Km i j → m i j (p,x)=0),
      ∀ i j : Fin 3, ∀ p ∈ K, ∀ᶠ z in 𝓝 p,
        let Q := commonSupportCoefficientFamily 3 (m i j) (hm i j) (Km i j) (hKm i j) (hmz i j) z
        nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q = NH i j z ∧
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = NL i j z ∧
        nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = NN i j z := by
  classical
  have hex (i j : Fin 3) := exists_referenceJacobi_commonSupport_boundary_multiplier_germs
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j K hK hInv
  choose m hm Km hKm hmz hGerm using hex
  exact ⟨m,hm,Km,hKm,hmz,hGerm⟩

private lemma actualJacobi_high_half (i j : Fin 3) (p : Pphys) (u : Hi) :
    IH ((NH i j p) u) = (NL i j p) (IH u) := by
  have hCoeff : coefficientValue 3 (NJ3 i j p) = coefficientValue 2 (NJ2 i j p) := by
    unfold referenceJacobiBoundaryThreeHalfCoefficientFamily
    exact coefficientValue_compactCoefficient 3 _ _ _
  exact congrArg (fun A : Hi →L[ℝ] Half => A u)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
      (NJ3 i j p) (NJ2 i j p) hCoeff)

private lemma actualJacobi_half_negative (i j : Fin 3) (p : Pphys) (v : Half) :
    JL ((NL i j p) v) = (NN i j p) (JL v) :=
  v017_native_half_negative hcalc hF hO hD τ0 (NJ2 i j p) v

private lemma zeroCorrection_high_half (i : Fin 3) (p : Pphys) (u : Hi) :
    IH (ZH i p u) = ZL i p (IH u) := by
  exact finiteTriple_compat IH p.2.2
    (fun _j : Fin 3 => Dr (3/2 : ℝ) p) (fun j => Mh j) (fun j : Fin 3 => NH i j p)
    (fun _j : Fin 3 => Dr (1/2 : ℝ) p) (fun j => Ml j) (fun j : Fin 3 => NL i j p)
    (fun _j z => sphereSobolevInclusionL_radialDriftAdjoint hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (referenceCenterDrift g L p.1 p.2.1) z)
    (fun j z => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (EuclideanSpace.single j (1 : ℝ)) z)
    (fun j z => actualJacobi_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j p z) u

private lemma zeroCorrection_half_negative (i : Fin 3) (p : Pphys) (v : Half) :
    JL (ZL i p v) = ZN i p (JL v) := by
  exact finiteTriple_compat JL p.2.2
    (fun _j : Fin 3 => Dr (1/2 : ℝ) p) (fun j => Ml j) (fun j : Fin 3 => NL i j p)
    (fun _j : Fin 3 => Dr (-(1/2 : ℝ)) p) (fun j => Mn j) (fun j : Fin 3 => NN i j p)
    (fun _j z => sphereSobolevInclusionL_radialDriftAdjoint hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (referenceCenterDrift g L p.1 p.2.1) z)
    (fun j z => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (EuclideanSpace.single j (1 : ℝ)) z)
    (fun j z => actualJacobi_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j p z) v

private lemma zeroReverse_high_half (i : Fin 3) (p : Pphys) (u : Hi) :
    IH (zH i p u) = zL i p (IH u) := by
  exact finiteTriple_compat IH p.2.2
    (fun j : Fin 3 => NH i j p) (fun j => Mh j) (fun _j : Fin 3 => dr (3/2 : ℝ) p)
    (fun j : Fin 3 => NL i j p) (fun j => Ml j) (fun _j : Fin 3 => dr (1/2 : ℝ) p)
    (fun j z => actualJacobi_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j p z)
    (fun j z => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (EuclideanSpace.single j (1 : ℝ)) z)
    (fun _j z => sphereSobolevInclusionL_radialDrift hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (referenceCenterDrift g L p.1 p.2.1) z) u

private lemma zeroReverse_half_negative (i : Fin 3) (p : Pphys) (v : Half) :
    JL (zL i p v) = zN i p (JL v) := by
  exact finiteTriple_compat JL p.2.2
    (fun j : Fin 3 => NL i j p) (fun j => Ml j) (fun _j : Fin 3 => dr (1/2 : ℝ) p)
    (fun j : Fin 3 => NN i j p) (fun j => Mn j) (fun _j : Fin 3 => dr (-(1/2 : ℝ)) p)
    (fun j z => actualJacobi_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j p z)
    (fun j z => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (EuclideanSpace.single j (1 : ℝ)) z)
    (fun _j z => sphereSobolevInclusionL_radialDrift hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (referenceCenterDrift g L p.1 p.2.1) z) v

private lemma zeroCorrection_pairing (i : Fin 3) (p : Pphys) (v : Half) (n : Neg) :
    PP (ZL i p v) n = PP v (zN i p n) := by
  change ⟪ZL i p v,n⟫_ℝ = ⟪v,zN i p n⟫_ℝ
  simp only [zeroCorrectionHalf,zeroReverseNegative,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  refine congrArg (fun z : ℝ => p.2.2*z) ?_
  apply Finset.sum_congr rfl
  intro j hj
  have hDr := sphereSobolevDualPairing_radialDriftAdjoint hF hO hD
    (1/2 : ℝ) (referenceCenterDrift g L p.1 p.2.1) ((Ml j) ((NL i j p) v)) n
  have hM := sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD
    (EuclideanSpace.single j 1) ((dr (-(1/2 : ℝ)) p) n) ((NL i j p) v)
  have hN := v017_native_pairing hcalc hF hO hD τ0 (NJ2 i j p) v
    ((Mn j) ((dr (-(1/2 : ℝ)) p) n))
  exact hDr.trans (hM.symm.trans hN)

/-- Exact direct low extension of the complete forward E word. No low norm is inferred. -/
theorem canonicalHigh_low_compatibility
    (hreg : FixedDirichletRegularity) (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiH : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q = PiH i t)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (u : Hi) : JL (EH i t u) = EL i t (IH u) := by
  have hPi (v : Hi) : IH (PiH i t v)=PiL i t (IH v) := by
    rw [← hPiH,← hPiL]
    exact v017_native_high_half hcalc hF hO hD τ0 Q v
  have hRad (v : Hi) : JL (Th t.1 (PiH i t v))=Tl t.1 (PiL i t (IH v)) :=
    (v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg (PiH i t v)).trans
      (congrArg (Tl t.1) (hPi v))
  have hAng (j : Fin 3) (v : Hi) : JL (raisingHigh hF hO hD j ((NH i j t.1) v))=
      raisingLow hF hO hD j ((NL i j t.1) (IH v)) :=
    (v017_inclusion_raisingHigh hF hO hD j ((NH i j t.1) v)).trans
      (congrArg (raisingLow hF hO hD j)
        (actualJacobi_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t.1 v))
  unfold canonicalHigh canonicalLow
  exact finiteFirstOrder_compat IH JL ((Th t.1).comp (PiH i t)) ((Tl t.1).comp (PiL i t))
    (fun j => (raisingHigh hF hO hD j).comp (NH i j t.1))
    (fun j => (raisingLow hF hO hD j).comp (NL i j t.1)) (ZH i t.1) (ZL i t.1) hRad hAng
    (zeroCorrection_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t.1) u

private lemma orderedReverseHigh_low_compatibility
    (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (hPiN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i t)
    (u : Hi) : JL (eH i t u) = eL i t (IH u) := by
  have hPi (v : Half) : JL (PiL i t v)=PiN i t (JL v) := by
    rw [← hPiL,← hPiN]
    exact v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) v
  have hRad (v : Hi) : JL (PiL i t (Sh t.1 v))=PiN i t (Sl t.1 (IH v)) :=
    (hPi (Sh t.1 v)).trans (congrArg (PiN i t)
      (v016_actual_Sh_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData t.1 hSeg v).symm)
  have hAng (j : Fin 3) (v : Hi) : JL ((NL i j t.1) (loweringHigh hF hO hD j v))=
      (NN i j t.1) (loweringLow hF hO hD j (IH v)) :=
    (actualJacobi_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t.1
      (loweringHigh hF hO hD j v)).trans
      (congrArg (NN i j t.1) (v017_inclusion_loweringHigh hF hO hD j v))
  unfold orderedReverseHigh orderedReverseLow
  exact finiteFirstOrder_compat IH JL ((PiL i t).comp (Sh t.1)) ((PiN i t).comp (Sl t.1))
    (fun j => (NL i j t.1).comp (loweringHigh hF hO hD j))
    (fun j => (NN i j t.1).comp (loweringLow hF hO hD j)) (zH i t.1) (zL i t.1) hRad hAng
    (zeroReverse_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t.1) u

private lemma canonicalLow_orderedReverseLow_pairing
    (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (hPiN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i t)
    (x y : Half) : PP x (EL i t y) = PP y (eL i t x) := by
  have hPi (v : Half) (n : Neg) : PP (PiL i t v) n = PP v (PiN i t n) := by
    rw [← hPiL,← hPiN]
    exact v017_native_pairing hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) v n
  have hRad : PP x (Tl t.1 (PiL i t y)) = PP y (PiN i t (Sl t.1 x)) :=
    (v016_actual_pairing_Sl_Tl hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData t.1 hSeg x (PiL i t y)).symm.trans (hPi y (Sl t.1 x))
  have hAng (j : Fin 3) : PP x (raisingLow hF hO hD j ((NL i j t.1) y)) =
      PP y ((NN i j t.1) (loweringLow hF hO hD j x)) :=
    (v017_pairing_loweringLow_raisingLow hF hO hD j ((NL i j t.1) y) x).symm.trans
      (v017_native_pairing hcalc hF hO hD τ0 (NJ2 i j t.1) y (loweringLow hF hO hD j x))
  have hZero : PP x (JL (ZL i t.1 y)) = PP y (JL (zL i t.1 x)) := by
    have h1 := v016_pairing_inclusion_symm (ZL i t.1 y) x
    have h2 := zeroCorrection_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t.1 y (JL x)
    have h3 := zeroReverse_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t.1 x
    exact h1.symm.trans (h2.trans (congrArg (PP y) h3.symm))
  change ⟪x,EL i t y⟫_ℝ = ⟪y,eL i t x⟫_ℝ
  simp only [canonicalLow,orderedReverseLow,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,inner_add_right,inner_sum]
  exact congrArg₂ (fun c z : ℝ => c+z)
    (congrArg₂ (fun r a : ℝ => r+a) hRad (Finset.sum_congr rfl (fun j _ => hAng j))) hZero


/-- Exact low reverse pairing, exposed with literal ordered operators for full E/E assembly. -/
theorem canonicalLow_explicit_ordered_reverse_pairing
    (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (hPiN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i t)
    (x y : Half) : PP x (EL i t y) = PP y
      (((PiN i t).comp (Sl t.1) +
        (∑ j : Fin 3, (NN i j t.1).comp (loweringLow hF hO hD j)) +
          (JL).comp (zL i t.1)) x) := by
  simpa only [orderedReverseLow] using
    (canonicalLow_orderedReverseLow_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      i t hSeg Q hPiL hPiN x y)

/-- Exact high/low compatibility of the literal ordered reverse operators. -/
theorem explicit_ordered_reverse_high_low_compatibility
    (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (hPiN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i t)
    (u : Hi) : JL
      (((PiL i t).comp (Sh t.1) +
        (∑ j : Fin 3, (NL i j t.1).comp (loweringHigh hF hO hD j)) +
          (IH).comp (zH i t.1)) u) =
      ((PiN i t).comp (Sl t.1) +
        (∑ j : Fin 3, (NN i j t.1).comp (loweringLow hF hO hD j)) +
          (JL).comp (zL i t.1)) (IH u) := by
  simpa only [orderedReverseHigh, orderedReverseLow] using
    (orderedReverseHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      i t hSeg Q hPiL hPiN u)

/-- The genuine full E pivot is obtained from the actual radial, angular,
coordinate, native multiplier and radial drift pairings. -/
theorem canonicalHigh_genuine_ordered_reverse_pivot
    (hreg : FixedDirichletRegularity) (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiH : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q = PiH i t)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (hPiN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i t)
    (u v : Hi) :
    PP (EH i t u) (JL (IH v)) = PP (IH u)
      (JL (((PiL i t).comp (Sh t.1) +
        (∑ j : Fin 3, (NL i j t.1).comp (loweringHigh hF hO hD j)) +
          (IH).comp (zH i t.1)) v)) := by
  have hForward := canonicalHigh_low_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg i t hSeg Q hPiH hPiL u
  have hReverse := orderedReverseHigh_low_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t hSeg Q hPiL hPiN v
  have hLow := canonicalLow_orderedReverseLow_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t hSeg Q hPiL hPiN (IH v) (IH u)
  have hStart := v016_pairing_inclusion_symm (EH i t u) (IH v)
  change _ = PP (IH u) (JL (eH i t v))
  exact hStart.trans ((congrArg (PP (IH v)) hForward).trans
    (hLow.trans (congrArg (PP (IH u)) hReverse.symm)))


private lemma native_commonSupport_contDiff {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0) :
    ContDiff ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 m hm K hK hz p)) ∧
    ContDiff ℝ ∞ (fun p => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) ∧
    ContDiff ℝ ∞ (fun p => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) := by
  have hh := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 m hm K hK hz
  have hl : ContDiff ℝ ∞ (fun p => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 m hm K hK hz)
  have hAdj : ContDiff ℝ ∞ (fun A : Half →L[ℝ] Half => realHalfOperatorAdjointL A) :=
    ContinuousLinearMap.contDiff _
  exact ⟨hh,hl,by simpa only [nativeNegativeHalfCoefficientMulL,Function.comp_def] using hAdj.comp hl⟩

private lemma zeroWords_contDiffAt (t : Tpar)
    (hNH : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NH i j z.1) t)
    (hNL : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NL i j z.1) t)
    (hNN : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NN i j z.1) t) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z : Tpar => ZH i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => ZL i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => ZN i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => zH i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => zL i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => zN i z.1) t := by
  have hProj : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDr (s : ℝ) : ContDiffAt ℝ ∞ (fun z : Tpar => Dr s z.1) t :=
    ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffAt
  have hdr (s : ℝ) : ContDiffAt ℝ ∞ (fun z : Tpar => dr s z.1) t :=
    ((contDiff_reference_sphereSobolevRadialDriftL g hg L hF hO hD s).comp hProj).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiffAt_fst.snd.snd
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNH i j))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNL i j))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNN i j))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hNH i j).clm_comp (contDiffAt_const.clm_comp (hdr _))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hNL i j).clm_comp (contDiffAt_const.clm_comp (hdr _))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hNN i j).clm_comp (contDiffAt_const.clm_comp (hdr _))))

/-- Ordinary smoothness of all four full E endpoints, before gain assembly. -/
private lemma canonicalEndpoints_contDiffAt
    (hreg : FixedDirichletRegularity) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hNH : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NH i j z.1) t)
    (hNL : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NL i j z.1) t)
    (hNN : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NN i j z.1) t)
    (hPiH : ∀ i : Fin 3, ContDiffAt ℝ ∞ (PiH i) t)
    (hPiL : ∀ i : Fin 3, ContDiffAt ℝ ∞ (PiL i) t)
    (hPiN : ∀ i : Fin 3, ContDiffAt ℝ ∞ (PiN i) t) (i : Fin 3) :
    ContDiffAt ℝ ∞ (EH i) t ∧ ContDiffAt ℝ ∞ (EL i) t ∧
    ContDiffAt ℝ ∞ (eH i) t ∧ ContDiffAt ℝ ∞ (eL i) t := by
  have hRem := contDiffAt_actualAngularRadialRemainder_families_of_segment
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg
  have hTh := hRem.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hTl := hRem.2.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hSh := hRem.2.2.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hSl := hRem.2.2.2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst
  have hZ := zeroWords_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    t hNH hNL hNN i
  refine ⟨?_,?_,?_,?_⟩
  · exact ((hTh.clm_comp (hPiH i)).add
      (ContDiffAt.sum (fun j _ => contDiffAt_const.clm_comp (hNH i j)))).add
        (contDiffAt_const.clm_comp hZ.1)
  · exact ((hTl.clm_comp (hPiL i)).add
      (ContDiffAt.sum (fun j _ => contDiffAt_const.clm_comp (hNL i j)))).add
        (contDiffAt_const.clm_comp hZ.2.1)
  · exact (((hPiL i).clm_comp hSh).add
      (ContDiffAt.sum (fun j _ => (hNL i j).clm_comp contDiffAt_const))).add
        (contDiffAt_const.clm_comp hZ.2.2.2.1)
  · exact (((hPiN i).clm_comp hSl).add
      (ContDiffAt.sum (fun j _ => (hNN i j).clm_comp contDiffAt_const))).add
        (contDiffAt_const.clm_comp hZ.2.2.2.2.1)

/-- The genuine H0/E gained row: ordinary order one at both canonical endpoints. -/
def zeroReverseEHigh (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (zL i t.1).comp (EH j t) - (EH j t).comp (zH i t.1)
def zeroReverseELow (i j : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (zN i t.1).comp (EL j t) - (EL j t).comp (zL i t.1)

attribute [local irreducible] canonicalHigh canonicalLow zeroReverseHigh zeroReverseHalf zeroReverseNegative

/-- Exact ordered H0/E graph at one literal current t; no gain assumption. -/
theorem zeroReverseEHigh_graph
    (hreg : FixedDirichletRegularity) (i j : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiH : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q = PiH j t)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL j t)
    (u : Hi) :
    JL (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t u) =
      zN i t.1 (EL j t (IH u)) - EL j t (zL i t.1 (IH u)) := by
  let EHi : Hi →L[ℝ] Half := EH j t
  let ELo : Half →L[ℝ] Neg := EL j t
  let zHi : Hi →L[ℝ] Hi := zH i t.1
  let zLi : Half →L[ℝ] Half := zL i t.1
  let zNi : Neg →L[ℝ] Neg := zN i t.1
  have hE : ∀ v : Hi, JL (EHi v)=ELo (IH v) :=
    canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg j t hSeg Q hPiH hPiL
  have hZ : ∀ v : Half, JL (zLi v)=zNi (JL v) :=
    zeroReverse_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t.1
  have hH : ∀ v : Hi, IH (zHi v)=zLi (IH v) :=
    zeroReverse_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t.1
  change JL ((zLi.comp EHi-EHi.comp zHi) u)=zNi (ELo (IH u))-ELo (zLi (IH u))
  exact orderedZeroReverse_graph IH JL EHi ELo zHi zLi zNi hE hZ hH u

/-- Both H0/E norm estimates are ordinary products of their own endpoint norms. -/
theorem zeroReverseE_norm_bounds (i j : Fin 3) (t : Tpar) :
    ‖zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t‖ ≤
      ‖zL i t.1‖*‖EH j t‖ + ‖EH j t‖*‖zH i t.1‖ ∧
    ‖zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t‖ ≤
      ‖zN i t.1‖*‖EL j t‖ + ‖EL j t‖*‖zL i t.1‖ := by
  constructor
  · change ‖(zL i t.1).comp (EH j t)-(EH j t).comp (zH i t.1)‖ ≤ _
    exact norm_orderedZeroRow_le (zL i t.1) (EH j t) (zH i t.1)
  · change ‖(zN i t.1).comp (EL j t)-(EL j t).comp (zL i t.1)‖ ≤ _
    exact norm_orderedZeroRow_le (zN i t.1) (EL j t) (zL i t.1)

/-- Actual original Pi and actual Jacobi germs sharing one physical room.
The support witnesses are retained for subsequent gained finite assembly. -/
structure CoefficientGermRoom (δ : ℝ) where
  piScalar : Fin 3 → Tpar × R3 → ℝ
  piSmooth : ∀ i, ContDiff ℝ ∞ (piScalar i)
  piSupport : Set R3
  piCompact : IsCompact piSupport
  piZero : ∀ i t x, x ∉ piSupport → piScalar i (t,x)=0
  piGerm : ∀ i : Fin 3, ∀ t ∈ (commonRoom y0 ρ δ) ×ˢ closedBall (0 : R3 →L[ℝ] ℝ) 1,
    ∀ᶠ z in 𝓝 t,
      let Q := commonSupportCoefficientFamily 3 (piScalar i) (piSmooth i) piSupport piCompact (piZero i) z
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q = PiH i z ∧
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i z ∧
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i z
  jacobiScalar : Fin 3 → Fin 3 → Pphys × R3 → ℝ
  jacobiSmooth : ∀ i j, ContDiff ℝ ∞ (jacobiScalar i j)
  jacobiSupport : Fin 3 → Fin 3 → Set R3
  jacobiCompact : ∀ i j, IsCompact (jacobiSupport i j)
  jacobiZero : ∀ i j p x, x ∉ jacobiSupport i j → jacobiScalar i j (p,x)=0
  jacobiGerm : ∀ i j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ,
    ∀ᶠ z in 𝓝 p,
      let Q := commonSupportCoefficientFamily 3 (jacobiScalar i j) (jacobiSmooth i j)
        (jacobiSupport i j) (jacobiCompact i j) (jacobiZero i j) z
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q = NH i j z ∧
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = NL i j z ∧
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = NN i j z

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Geometry projected from one original finite-room guard. The original
ellipticity, drift and strong-inverse witnesses remain internal to this proof;
both returned geometry facts use the same original room and Jacobian. -/
private lemma exists_actual_finite_room_geometry
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ commonRoom y0 ρ d ⊆ Ω ∧
      ∀ p ∈ commonRoom y0 ρ d, ∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,ξ.val))).IsInvertible := by
  obtain ⟨lam,Lam,d,_hlam,hd,hdρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  refine ⟨d,hd,hdρ,?_,?_⟩
  · intro p hp
    exact (hFin p hp).2.2.1
  · intro p hp ξ
    exact (hFin p hp).2.2.2.2 ξ

private def ordinaryEndpointsFoldedContract : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ W : CoeffRoom δ,
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (EH i) t ∧ ContDiffAt ℝ ∞ (EL i) t ∧
        ContDiffAt ℝ ∞ (eH i) t ∧ ContDiffAt ℝ ∞ (eL i) t) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (EH i t u) = EL i t (IH u) ∧ JL (eH i t u) = eL i t (IH u)) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v : Hi,
        PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (eH i t v))) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t ∧
        ContDiffAt ℝ ∞ (zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t u) =
          zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t (IH u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ, ∀ i : Fin 3,
        ‖iteratedFDeriv ℝ n (EH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (EL i) t‖ ≤ M ∧
        ‖iteratedFDeriv ℝ n (eH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (eL i) t‖ ≤ M ∧
        ∀ j : Fin 3,
          ‖iteratedFDeriv ℝ n (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t‖ ≤ M ∧
          ‖iteratedFDeriv ℝ n (zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t‖ ≤ M)

attribute [local irreducible] ordinaryEndpointsFoldedContract

private theorem ordinaryEndpointsFoldedContract_proof (hreg : FixedDirichletRegularity) :
    ordinaryEndpointsFoldedContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 := by
  classical
  obtain ⟨dF,hdF,hdFρ,hRoomF,hInvF⟩ := exists_actual_finite_room_geometry
    (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg
  obtain ⟨dP,hdP,_hdPρ,mP,hmP,KP,hKP,hzP,hPG⟩ :=
    exists_referencePi_commonSupport_native_operator_germs
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let δ := min dF dP
  have hδ : 0 < δ := lt_min hdF hdP
  have hSubF : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dF := commonRoom_mono y0 ρ (min_le_left _ _)
  have hSubP : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dP := commonRoom_mono y0 ρ (min_le_right _ _)
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := fun p hp => hRoomF (hSubF hp)
  have hInv : ∀ p ∈ commonRoom y0 ρ δ, ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,ξ.val))).IsInvertible :=
    fun p hp => hInvF p (hSubF hp)
  obtain ⟨mN,hmN,KN,hKN,hzN,hNG⟩ := exists_actualJacobi_native_germs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      (commonRoom y0 ρ δ) (isCompact_commonRoom y0 ρ δ) hInv
  let W : CoeffRoom δ :=
    { piScalar := mP, piSmooth := hmP, piSupport := KP, piCompact := hKP, piZero := hzP,
      piGerm := fun i t ht => hPG i t ⟨hSubP ht.1,ht.2⟩,
      jacobiScalar := mN, jacobiSmooth := hmN, jacobiSupport := KN, jacobiCompact := hKN,
      jacobiZero := hzN, jacobiGerm := hNG }
  have hPiAt (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (PiH i) t ∧ ContDiffAt ℝ ∞ (PiL i) t ∧ ContDiffAt ℝ ∞ (PiN i) t := by
    have hs := native_commonSupport_contDiff hcalc hF hO hD τ0 (W.piScalar i) (W.piSmooth i)
      W.piSupport W.piCompact (W.piZero i)
    have hgerm := W.piGerm i t ht
    exact ⟨hs.1.contDiffAt.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.1.symm)),
      hs.2.1.contDiffAt.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.1.symm)),
      hs.2.2.contDiffAt.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.2.symm))⟩
  have hNAt (i j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) :
      ContDiffAt ℝ ∞ (fun z => NH i j z) p ∧
      ContDiffAt ℝ ∞ (fun z => NL i j z) p ∧
      ContDiffAt ℝ ∞ (fun z => NN i j z) p := by
    have hs := native_commonSupport_contDiff hcalc hF hO hD τ0 (W.jacobiScalar i j) (W.jacobiSmooth i j)
      (W.jacobiSupport i j) (W.jacobiCompact i j) (W.jacobiZero i j)
    have hgerm := W.jacobiGerm i j p hp
    exact ⟨hs.1.contDiffAt.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.1.symm)),
      hs.2.1.contDiffAt.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.1.symm)),
      hs.2.2.contDiffAt.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.2.symm))⟩
  have hSeg (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
  have hAt (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (EH i) t ∧ ContDiffAt ℝ ∞ (EL i) t ∧
      ContDiffAt ℝ ∞ (eH i) t ∧ ContDiffAt ℝ ∞ (eL i) t :=
    canonicalEndpoints_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg t (hSeg t ht)
      (fun i j => (hNAt i j t.1 ht.1).1.comp t contDiffAt_fst)
      (fun i j => (hNAt i j t.1 ht.1).2.1.comp t contDiffAt_fst)
      (fun i j => (hNAt i j t.1 ht.1).2.2.comp t contDiffAt_fst)
      (fun i => (hPiAt i t ht).1) (fun i => (hPiAt i t ht).2.1) (fun i => (hPiAt i t ht).2.2) i
  have hGainAt (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t ∧
      ContDiffAt ℝ ∞ (zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t := by
    have hZ := zeroWords_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t
      (fun i j => (hNAt i j t.1 ht.1).1.comp t contDiffAt_fst)
      (fun i j => (hNAt i j t.1 ht.1).2.1.comp t contDiffAt_fst)
      (fun i j => (hNAt i j t.1 ht.1).2.2.comp t contDiffAt_fst) i
    have hE := hAt j t ht
    exact ⟨(hZ.2.2.2.2.1.clm_comp hE.1).sub (hE.1.clm_comp hZ.2.2.2.1),
      (hZ.2.2.2.2.2.clm_comp hE.2.1).sub (hE.2.1.clm_comp hZ.2.2.2.2.1)⟩
  unfold ordinaryEndpointsFoldedContract
  refine ⟨δ,hδ,(min_le_left _ _).trans hdFρ,hRoom,W,hAt,?_,?_,hGainAt,?_,?_⟩
  · intro i t ht u
    have hP := (W.piGerm i t ht).self_of_nhds
    exact ⟨canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg i t (hSeg t ht) _ hP.1 hP.2.1 u,
      orderedReverseHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        i t (hSeg t ht) _ hP.2.1 hP.2.2 u⟩
  · intro i t ht u v
    have hP := (W.piGerm i t ht).self_of_nhds
    exact canonicalHigh_genuine_ordered_reverse_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg i t (hSeg t ht) _ hP.1 hP.2.1 hP.2.2 u v
  · intro i j t ht u
    have hP := (W.piGerm j t ht).self_of_nhds
    exact zeroReverseEHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg i j t (hSeg t ht) _ hP.1 hP.2.1 u
  · intro N
    have hK : IsCompact (ParamRoom δ) := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
    let cap1 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (EH) (ParamRoom δ) hK (fun i t ht => (hAt i t ht).1) N
    let M1 : ℝ := Classical.choose cap1
    have hM10 : 0 ≤ M1 := (Classical.choose_spec cap1).1
    have hM1 := (Classical.choose_spec cap1).2
    let cap2 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (EL) (ParamRoom δ) hK (fun i t ht => (hAt i t ht).2.1) N
    let M2 : ℝ := Classical.choose cap2
    have hM20 : 0 ≤ M2 := (Classical.choose_spec cap2).1
    have hM2 := (Classical.choose_spec cap2).2
    let cap3 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (eH) (ParamRoom δ) hK (fun i t ht => (hAt i t ht).2.2.1) N
    let M3 : ℝ := Classical.choose cap3
    have hM30 : 0 ≤ M3 := (Classical.choose_spec cap3).1
    have hM3 := (Classical.choose_spec cap3).2
    let cap4 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (eL) (ParamRoom δ) hK (fun i t ht => (hAt i t ht).2.2.2) N
    let M4 : ℝ := Classical.choose cap4
    have hM40 : 0 ≤ M4 := (Classical.choose_spec cap4).1
    have hM4 := (Classical.choose_spec cap4).2
    let cap5 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (fun ij : Fin 3 × Fin 3 => zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ij.1 ij.2)
      (ParamRoom δ) hK (fun ij t ht => (hGainAt ij.1 ij.2 t ht).1) N
    let M5 : ℝ := Classical.choose cap5
    have hM50 : 0 ≤ M5 := (Classical.choose_spec cap5).1
    have hM5 := (Classical.choose_spec cap5).2
    let cap6 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (fun ij : Fin 3 × Fin 3 => zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ij.1 ij.2)
      (ParamRoom δ) hK (fun ij t ht => (hGainAt ij.1 ij.2 t ht).2) N
    let M6 : ℝ := Classical.choose cap6
    have hM60 : 0 ≤ M6 := (Classical.choose_spec cap6).1
    have hM6 := (Classical.choose_spec cap6).2
    refine ⟨M1+M2+M3+M4+M5+M6,by linarith,?_⟩
    intro n hn t ht i
    exact ⟨(hM1 n hn t ht i).trans (by linarith),
      (hM2 n hn t ht i).trans (by linarith),
      (hM3 n hn t ht i).trans (by linarith),
      (hM4 n hn t ht i).trans (by linarith),
      fun j => ⟨(hM5 n hn t ht (i,j)).trans (by linarith),
        (hM6 n hn t ht (i,j)).trans (by linarith)⟩⟩


/-- Complete ordinary endpoints of the smooth ordered E extension, with genuine reverse and shared current
Pi/Jacobi germs, and ambient finite-jet caps chosen before profiles and inputs.
The signed room includes r=0. Literal original moving E is identified only by
`movingDifferenceQuotient_eq_canonicalHigh` with its retained nonzero-radius
hypothesis; no equality or smoothness of the original quotient at zero is asserted.
This owner does not claim the missing full E/E gain family. -/
theorem exists_commonRoom_actual_fullE_ordinary_endpoints
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ W : CoeffRoom δ,
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (EH i) t ∧ ContDiffAt ℝ ∞ (EL i) t ∧
        ContDiffAt ℝ ∞ (eH i) t ∧ ContDiffAt ℝ ∞ (eL i) t) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (EH i t u) = EL i t (IH u) ∧ JL (eH i t u) = eL i t (IH u)) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v : Hi,
        PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (eH i t v))) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t ∧
        ContDiffAt ℝ ∞ (zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t u) =
          zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t (IH u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ, ∀ i : Fin 3,
        ‖iteratedFDeriv ℝ n (EH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (EL i) t‖ ≤ M ∧
        ‖iteratedFDeriv ℝ n (eH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (eL i) t‖ ≤ M ∧
        ∀ j : Fin 3,
          ‖iteratedFDeriv ℝ n (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t‖ ≤ M ∧
          ‖iteratedFDeriv ℝ n (zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) t‖ ≤ M) := by
  simpa only [ordinaryEndpointsFoldedContract] using
    (ordinaryEndpointsFoldedContract_proof g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedEndpoints

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedEndpoints.movingDifferenceQuotient_eq_canonicalHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedEndpoints.exists_commonRoom_actual_fullE_ordinary_endpoints
