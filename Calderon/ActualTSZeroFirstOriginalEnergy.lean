import Calderon.ActualTSZeroFirstRegularity
import Calderon.ActualTSZeroFirstSymmetricIntegral

/-! Original factor-four D01 estimate.
All row constants, room witnesses and threshold are produced internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  AmbientReferenceRaising ActualGeneratorEPairedGainedEndpoints
  ActualAllAngularAtomGainedRoom ActualHigherSFormation ActualRetainedGeneratorMultiplierGains
  ActualTSZeroFirstLiteralWords ActualTSZeroFirstPointwise ActualTSZeroFirstEnergyTools
  ActualTSZeroFirstRegularity ActualTSZeroFirstSymmetricIntegral
  ActualHigherSScalarCommutatorForm ActualHigherSZeroScalarCommutatorForm
  ActualHigherSZeroScalarNativeForm
  ActualTSPrincipalLowerReferenceOrders PrincipalCommutator
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

abbrev ZeroFirstWordIndex := Fin 3 × Fin 3 × Fin 3 × Generator

private lemma card_zeroFirstWordIndex : Fintype.card ZeroFirstWordIndex = 270 := by
  norm_num [ZeroFirstWordIndex,Generator,Fintype.card_prod,Fintype.card_sum]

private lemma abs_sum_le_card_mul {ι : Type*} [Fintype ι] (f : ι → ℝ) (A : ℝ)
    (h : ∀ z, |f z| ≤ A) : |∑ z, f z| ≤ (Fintype.card ι : ℝ)*A := by
  calc
    _ ≤ ∑ z, |f z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : ι, A := Finset.sum_le_sum (fun z _ => h z)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "UF" => higherSInput hO hD
local notation "D01" => originalZeroFirstCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "WD" => zeroFirstWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SD" => zeroFirstSymmetricWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CD" => zeroFirstCorrectionDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

/-- Exactly the 270 original symmetric word/coordinate occurrences. -/
def zeroFirstSymmetricSum (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ∑ z : ZeroFirstWordIndex, SD g2 q dr Ar p F z.1 z.2.1 z.2.2.1 z.2.2.2 x
local notation "SS" => zeroFirstSymmetricSum
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- The entire gained-plus-raw-correction remainder, with its original four. -/
def zeroFirstTotalRemainder (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  D01 g2 dr Ar p hdr hAr q F x-4*SS g2 q dr Ar p F x
local notation "RR" => zeroFirstTotalRemainder
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] nativeReferenceZeroCoefficient nativeReferenceAdjointZeroCoefficient
  canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  raisingHigh raisingLow loweringHigh loweringLow generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow sphereSobolevInclusionL sphereSobolevHalfToSphereL2L

/-- Complete original zero/first T/S estimate: no final budget or coefficient
cap is a premise, and no correction is discarded or reassigned. -/
theorem exists_original_zero_first_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ C01 eta01 : ℝ, 0 < C01 ∧ 0 < eta01 ∧ eta01 ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta01 →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*D01 g2 dr Ar p hdr hAr q F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*D01 g2 dr Ar p hdr hAr q F x| ≤
        C01*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨d,hd,_hdD,_hd0,_hdRho,_hInv,⟨P⟩⟩ := exists_same_packet_allAngularAtom_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  let G := Classical.choice (ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel d hd)
  obtain ⟨Cword,Ccorr,hCword,hCcorr,hRows⟩ := exists_original_zero_first_pointwise_row_bounds
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL P g2 hg2
  obtain ⟨Csym,etaSym,hCsym,hEtaSym,hEtaSym1,hSym⟩ := exists_original_zero_first_symmetric_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hd P g2 hg2
  obtain ⟨etaReg,hEtaReg,_hEtaReg1,hRegular⟩ := exists_original_zero_first_regularity
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hd P g2 hg2
  obtain ⟨Cr,hCr,hReference⟩ := exists_highInput_inclusion_reference_integral_bound
    hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Ccore : ℝ := 4*(270*Csym+270*Cword+9*Ccorr)
  let C01 : ℝ := Ccore*Cr
  let eta01 : ℝ := min data.eta0 (min G.epsG (min etaSym etaReg))
  have hCcore : 0 < Ccore := by dsimp only [Ccore]; positivity
  have hC01 : 0 < C01 := mul_pos hCcore hCr
  have hEta01 : 0 < eta01 := lt_min data.eta0_pos (lt_min G.epsG_pos (lt_min hEtaSym hEtaReg))
  refine ⟨C01,eta01,hC01,hEta01,min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hSupp hb hs
  have heG : eta ≤ G.epsG := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heSym : eta ≤ etaSym := he.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have heReg : eta ≤ etaReg := he.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have he1 : eta ≤ 1 := heSym.trans hEtaSym1
  have hRooms := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta heG K hK hKball F hSupp hb hs
  have hOriginalI := (hRegular q hq dr hdr hdr1 Ar hAr p hp eta heta heReg K hK hKball F hSupp hb hs).2.2
  have hSymRows (z : ZeroFirstWordIndex) :=
    hSym q hq dr hdr hdr1 Ar hAr p hp eta heta heSym K hK hKball F hSupp hb hs
      z.1 z.2.1 z.2.2.1 z.2.2.2
  let u := UF F
  let beta := actualReferenceBeta g L q dr Ar p
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let e : R3 → ℝ := fun x => inclusionEnergyDensity IH (beta x) u x
  let S := SS g2 q dr Ar p F
  let R := RR g2 q dr Ar p hdr hAr F
  let EI : ℝ := ∫ x, mu x*e x
  have hmu0 (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
  have hmu : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hbeta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hu0 (x : R3) (hx : x ∉ K) : u x=0 := highInput_eq_zero_off hO hD F x (fun hy => hx (hSupp hy))
  have heI : Integrable (fun x => mu x*e x) :=
    inclusionEnergy_integrable IH mu beta u K hK hmu hbeta (fun x => (hbpos x).ne') hu hu0
  have he0 (x : R3) : 0 ≤ e x := inclusionEnergyDensity_nonneg IH (beta x) u x (hbpos x).le
  have hEI0 : 0 ≤ EI := integral_nonneg (fun x => mul_nonneg (hmu0 x) (he0 x))
  let sf : ZeroFirstWordIndex → R3 → ℝ := fun z x => mu x*SD g2 q dr Ar p F z.1 z.2.1 z.2.2.1 z.2.2.2 x
  have hSI : Integrable (fun x => mu x*S x) := by
    simpa only [S,zeroFirstSymmetricSum,Finset.mul_sum] using
      integrable_finset_sum Finset.univ (fun z _ => (hSymRows z).1)
  have hSCap : |∫ x, mu x*S x| ≤ 270*Csym*eta*EI := by
    have h := abs_integral_finite_sum_le sf (Csym*eta) EI
      (fun z => (hSymRows z).1) (fun z => (hSymRows z).2)
    simpa only [sf,S,zeroFirstSymmetricSum,Finset.mul_sum,card_zeroFirstWordIndex,Nat.cast_ofNat,mul_assoc] using h
  have hRFun : (fun x => mu x*R x)=(fun x => mu x*D01 g2 dr Ar p hdr hAr q F x-4*(mu x*S x)) := by
    funext x
    dsimp only [R,zeroFirstTotalRemainder,S]
    ring
  have hRI : Integrable (fun x => mu x*R x) := by
    rw [hRFun]
    exact hOriginalI.sub (hSI.const_mul 4)
  let Crem : ℝ := 4*(270*Cword+9*Ccorr)
  have hCrem : 0 ≤ Crem := by dsimp only [Crem]; positivity
  have hRPoint (x : R3) : |R x| ≤ Crem*eta*e x := by
    by_cases hx : x ∈ tsupport F.val
    · have h := hRows q hq dr hdr hdr1 Ar hAr p hp eta heta he1 x
        (ball_subset_closedBall (hKball (hSupp hx))) (hRooms.1 x hx)
        (hb x (hSupp hx)) (hs x (hSupp hx)) F
      let wf : ZeroFirstWordIndex → ℝ := fun z =>
        WD g2 q dr Ar p F z.1 z.2.1 z.2.2.1 z.2.2.2 x-
          SD g2 q dr Ar p F z.1 z.2.1 z.2.2.1 z.2.2.2 x
      let cf : Fin 3 × Fin 3 → ℝ := fun z => CD P g2 q dr Ar p F z.1 z.2 x
      have hW : |∑ z, wf z| ≤ 270*Cword*eta*e x := by
        have hw := abs_sum_le_card_mul wf (Cword*eta*e x)
          (fun z => h.1 z.1 z.2.1 z.2.2.1 z.2.2.2)
        simpa only [card_zeroFirstWordIndex,Nat.cast_ofNat,mul_assoc] using hw
      have hC : |∑ z, cf z| ≤ 9*Ccorr*eta*e x := by
        have hc := abs_sum_le_card_mul cf (Ccorr*eta*e x) (fun z => h.2 z.1 z.2)
        have hCount : (Fintype.card (Fin 3 × Fin 3) : ℝ)=9 := by norm_num [Fintype.card_prod]
        simpa only [hCount,mul_assoc] using hc
      have hLiteral := original_zero_first_eq_all_words_add_full_correction
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
        P g2 q dr Ar p hdr hAr F x (hRooms.1 x hx)
      have hIdentity : R x=4*((∑ z, wf z)+(∑ z, cf z)) := by
        dsimp only [R,zeroFirstTotalRemainder,S,zeroFirstSymmetricSum]
        rw [hLiteral]
        simp only [wf,cf,ZeroFirstWordIndex,Fintype.sum_prod_type,Finset.sum_sub_distrib]
        ring
      rw [hIdentity,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      have hTriangle : |(∑ z, wf z)+(∑ z, cf z)| ≤ |∑ z, wf z|+|∑ z, cf z| := abs_add_le _ _
      exact (mul_le_mul_of_nonneg_left (hTriangle.trans (add_le_add hW hC)) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
        (by dsimp only [Crem]; ring)
    · have hU0 : UF F x=0 := highInput_eq_zero_off hO hD F x hx
      have hS0 : S x=0 := by
        dsimp only [S,zeroFirstSymmetricSum,zeroFirstSymmetricWordDensity]
        simp only [hU0,map_zero,zero_apply,mul_zero,add_zero,Finset.sum_const_zero]
      have hD0 := original_zero_first_eq_zero_off_tsupport hF hO hD g L y0 Φ B ε C ρ H a w hData
        hg hcalc τ0 g2 dr Ar p hdr hAr q F x hx
      have hR0 : R x=0 := by
        change D01 g2 dr Ar p hdr hAr q F x-4*S x=0
        rw [hD0,hS0]
        ring
      rw [hR0,abs_zero]
      exact mul_nonneg (mul_nonneg hCrem heta) (he0 x)
  have hRCap : |∫ x, mu x*R x| ≤ Crem*eta*EI :=
    weighted_integral_abs_le_of_pointwise mu R e (Crem*eta) hmu0 hRI heI hRPoint
  have hIntegral : (∫ x, mu x*D01 g2 dr Ar p hdr hAr q F x)=4*(∫ x, mu x*S x)+(∫ x, mu x*R x) := by
    have hFun : (fun x => mu x*D01 g2 dr Ar p hdr hAr q F x)=
        (fun x => 4*(mu x*S x)+mu x*R x) := by
      funext x
      dsimp only [R,zeroFirstTotalRemainder,S]
      ring
    rw [hFun,integral_add (hSI.const_mul 4) hRI,integral_const_mul]
  have hTotal : |∫ x, mu x*D01 g2 dr Ar p hdr hAr q F x| ≤ Ccore*eta*EI := by
    rw [hIntegral]
    have hTriangle := abs_add_le (4*(∫ x, mu x*S x)) (∫ x, mu x*R x)
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hTriangle
    exact (hTriangle.trans (add_le_add
      (mul_le_mul_of_nonneg_left hSCap (by norm_num : (0 : ℝ) ≤ 4)) hRCap)).trans_eq
        (by dsimp only [Ccore,Crem]; ring)
  have hFclosed : tsupport F.val ⊆ closedBall y0 ρ := hSupp.trans (hKball.trans ball_subset_closedBall)
  have hRef : EI ≤ Cr*(∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) :=
    hReference q hq dr Ar p hdr hAr hp F hFclosed (fun x hx => hb x (hSupp hx))
  refine ⟨hOriginalI,?_⟩
  exact hTotal.trans ((mul_le_mul_of_nonneg_left hRef (mul_nonneg hCcore.le heta)).trans_eq
    (by dsimp only [C01]; ring))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding.exists_original_zero_first_integral_bound
