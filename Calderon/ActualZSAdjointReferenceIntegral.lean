import Calderon.ActualZSAdjointPhysicalPairing
import Calderon.ActualZSAdjointPairingEnergy
import Calderon.ActualSAdjointFullProfileCap
import Calderon.ActualHigherSZeroScalarNativeForm
import Calderon.ActualReverseEOrdinaryCaps

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointReferenceIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualSAdjointSecondNegative ActualZHalfRealization
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualHigherSAdjointFormation
  ActualZSAdjointPhysicalPairing ActualZSAdjointPairingEnergy ActualSAdjointFullProfileCap
  ActualHigherSZeroScalarNativeForm ActualHigherSZeroScalarCommutatorForm
  ActualHigherSScalarCommutatorNativeForm ActualCommonFirstWordQuadraticAdjoint ActualReverseEOrdinaryCaps

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "PL" => halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed negDualSpace
attribute [local irreducible] halfDualPairingL sphereSobolevInclusionL
  referenceZHalf fullAdjointNegative higherSAdjointOut

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

/-- Original -4 Z/Sdag integral bound with all actual premises produced.
eta0 precedes g2; C_ZS is presently a fixed-g2 intermediate. -/
theorem exists_native_Z_Sdag_reference_integral_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (d : ℝ) (room : CRoom hreg d0 germs d) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 ∧ ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ C_ZS : ℝ, 0 < C_ZS ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            hreg d0 germs g2 dr Ar p hdr hAr q F x⟫_ℝ) ∧
      |∫ x, referenceDensityFamily g L (q,x)*
        (-4*⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            hreg d0 germs g2 dr Ar p hdr hAr q F x⟫_ℝ)| ≤
        C_ZS*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  classical
  obtain ⟨es,hes,hes1,hFull⟩ := exists_fullAdjoint_uniform_profile_norm_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg d0 germs d room
  let data := Classical.choice (exists_reverseEOrdinaryPhysicalCaps g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hL hreg d0 germs d room)
  obtain ⟨CZ,hCZ,hZcap⟩ := exists_referenceZHalf_uniform_beta_bound
    (hF := hF) (hO := hO) (hD := hD) g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cr,hCr,hReference⟩ := exists_highInput_inclusion_reference_integral_bound
    hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨min es data.eta0,lt_min hes data.eta0_pos,(min_le_left _ _).trans hes1,?_⟩
  intro g2 hg2
  obtain ⟨CS,hCS,hScap⟩ := hFull g2 hg2
  let Cp : ℝ := 9*(‖PL‖+1)*CZ*CS
  have hN : 0 < ‖PL‖+1 := add_pos_of_nonneg_of_pos (norm_nonneg PL) zero_lt_one
  have hCp : 0 < Cp := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 9) hN) hCZ) hCS
  refine ⟨4*Cp*Cr,mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hCp) hCr,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hSupp hBeta hSmall
  have heta1 : eta ≤ 1 := (heta0.trans (min_le_left _ _)).trans hes1
  have hFball : tsupport F.val ⊆ ball y0 ρ := hSupp.trans hKball
  have hFclosed : tsupport F.val ⊆ closedBall y0 ρ := hFball.trans ball_subset_closedBall
  have hT (x : R3) (hx : x ∈ tsupport F.val) :
      higherSParam L dr Ar p q x ∈
        Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1) := by
    have hc := data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta
      (heta0.trans (min_le_right _ _)) x (hFclosed hx) (hFball hx)
      (hBeta x (hSupp hx)) (hSmall x (hSupp hx))
    exact hc.1.self_of_nhds
  let U : R3 → Hi := higherSInput hO hD F
  let beta : R3 → ℝ := actualReferenceBeta g L q dr Ar p
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let z : R3 → SphereL2 := (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val
  let v : R3 → SphereL2 := higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs g2 dr Ar p hdr hAr q F
  let f : R3 → ℝ := fun x => ⟪z x,v x⟫_ℝ
  let energy : R3 → ℝ := fun x => inclusionEnergyDensity IH (beta x) U x
  have hI : Integrable (fun x => mu x*f x) :=
    integrable_native_Z_Sdag g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg d0 germs d room g2 hg2 dr Ar p hdr hAr q F hT
  have hMu (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
  have hMuCont : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hBetaCont : Continuous beta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hBetaPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hUSmooth : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hU0 (x : R3) (hx : x ∉ tsupport F.val) : U x = 0 := highInput_eq_zero_off hO hD F x hx
  have hEI : Integrable (fun x => mu x*energy x) :=
    inclusionEnergy_integrable IH mu beta U (tsupport F.val) F.property.2.1
      hMuCont hBetaCont (fun x => (hBetaPos x).ne') hUSmooth hU0
  have hDecode (x : R3) :
      KL (referenceZHalf hF hO hD g L q dr Ar p x (U x)) = z x :=
    referenceZHalf_finiteCore_decode (hF := hF) (hO := hO) (hD := hD)
      g hg L q dr Ar p hdr hAr F x
  have hPoint (x : R3) : |f x| ≤ Cp*eta*energy x := by
    by_cases hx : x ∈ tsupport F.val
    · have hxK := hSupp hx
      have hZx := hZcap q hq dr hdr hdr1 Ar hAr p hp x (hFclosed hx) (U x)
      have hSx := hScap q hq dr hdr hdr1 Ar hAr p hp eta heta
        (heta0.trans (min_le_left _ _)) x (hFclosed hx) (hFball hx)
        (hBeta x hxK) (hSmall x hxK) F
      have hPair := half_negative_pairing_profile_bound
        (referenceZHalf hF hO hD g L q dr Ar p x (U x))
        (fullAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x)
        CZ CS (beta x) (referenceRadius dr Ar p L x) eta ‖U x‖
        (fun i : Fin 3 => ‖IH (fderiv ℝ U x (coordinateDirection i))‖)
        hCZ.le hCS.le (hBeta x hxK) (referenceRadius_pos dr Ar p L x hdr hAr).le
        heta heta1 (norm_nonneg _) (fun _ => norm_nonneg _) (hSmall x hxK) hZx hSx
      have hPhysical := native_Z_Sdag_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg d0 germs d room g2 dr Ar p hdr hAr q F hT x hx
      have hAbs : |f x| =
          |sphereSobolevDualPairing (1/2 : ℝ)
            (referenceZHalf hF hO hD g L q dr Ar p x (U x))
            (fullAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
              g2 dr Ar p q F x)| :=
        congrArg abs hPhysical.symm
      have hEnergy :
          beta x*‖U x‖^2+(beta x)⁻¹*
            (∑ i : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection i))‖^2) = energy x := by
        dsimp only [energy,inclusionEnergyDensity,PrincipalCommutator.directionalFDeriv]
        ring
      exact (hAbs.le.trans hPair).trans_eq (congrArg (fun t : ℝ => Cp*eta*t) hEnergy)
    · have hz0 : z x = 0 := by
        calc
          _ = KL (referenceZHalf hF hO hD g L q dr Ar p x (U x)) := (hDecode x).symm
          _ = 0 := by rw [hU0 x hx,map_zero,map_zero]
      change |⟪z x,v x⟫_ℝ| ≤ Cp*eta*energy x
      rw [hz0,inner_zero_left,abs_zero]
      exact mul_nonneg (mul_nonneg hCp.le heta)
        (inclusionEnergyDensity_nonneg IH (beta x) U x (hBetaPos x).le)
  have hSigned := weighted_signed_integral_bound mu f energy Cp eta hMu hI hEI hPoint
  have hReferenceHere :
      (∫ x, mu x*energy x) ≤ Cr*(∫ x, mu x*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) :=
    hReference q hq dr Ar p hdr hAr hp F hFclosed (fun x hx => hBeta x (hSupp hx))
  have hScale :
      4*Cp*eta*(∫ x, mu x*energy x) ≤ (4*Cp*Cr)*eta*
        (∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) := by
    have hC0 : 0 ≤ 4*Cp*eta := mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCp.le) heta
    exact (mul_le_mul_of_nonneg_left hReferenceHere hC0).trans_eq (by ring)
  exact ⟨hI,hSigned.trans hScale⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointReferenceIntegral

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointReferenceIntegral.exists_native_Z_Sdag_reference_integral_bound
