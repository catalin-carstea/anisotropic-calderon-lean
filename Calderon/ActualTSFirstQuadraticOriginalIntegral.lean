import Calderon.ActualTSFirstQuadraticPhysicalSplit
import Calderon.ActualTSFirstQuadraticActualGreen
import Calderon.ActualTSFirstQuadraticGains
import Calderon.ActualHigherSCommonProfileRoomData
import Calderon.ActualHigherSZeroScalarNativeForm
import Calderon.ActualTSFirstLinearZeroIntegral

/-! Full original quadratic D10 integral producer draft; unvalidated. Before-code: ../T-S-first-quadratic-original-integral-before-source-nov04-day-v001/. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticOriginalIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTFirstPhysicalDictionary ActualTSLowerZeroZeroBinding ActualTSFirstLinearZeroPointwise
  ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorNativeForm
  ActualHigherSZeroScalarCommutatorForm ActualHigherSZeroScalarNativeForm
  ActualTSPrincipalLowerReferenceOrders PrincipalCommutator
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)

open ActualHigherSQuadraticZeroWords ActualHigherSQuadraticZeroQuartic
  ActualHigherSQuadraticZeroQuarticBounds ActualHigherSQuarticFactorization
  ActualAllAngularAtomGainedRoom ActualTSFirstQuadraticActualGreen
  ActualTSFirstQuadraticGains ActualTSFirstQuadraticPhysicalSplit

def quadRowMultiplier : ℝ := 4*3*3*(Fintype.card ZeroWord : ℝ)

private lemma quadRowMultiplier_pos : 0 < quadRowMultiplier := by
  have hc : (0 : ℝ) < (Fintype.card ZeroWord : ℝ) := by exact_mod_cast Fintype.card_pos
  dsimp only [quadRowMultiplier]
  positivity

private lemma finite_sum_abs_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (B : ℝ) (hb : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ (Fintype.card ι : ℝ)*B := by
  calc
    _ ≤ ∑ i, |f i| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := f)
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp

private lemma finite_integral_sum_bound {ι : Type*} [Fintype ι]
    (f : ι → R3 → ℝ) (B : ℝ) (hi : ∀ i, Integrable (f i))
    (hb : ∀ i, |∫ x, f i x| ≤ B) :
    Integrable (fun x => ∑ i, f i x) ∧
      |∫ x, ∑ i, f i x| ≤ (Fintype.card ι : ℝ)*B := by
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hi i),?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact finite_sum_abs_bound (fun i => ∫ x, f i x) B hb

private lemma rows_abs_bound (f : Fin 3 → Fin 3 → ZeroWord → ℝ) (B : ℝ)
    (hb : ∀ l i z, |f l i z| ≤ B) :
    |4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, f l i z| ≤ quadRowMultiplier*B := by
  have hz l i := finite_sum_abs_bound (f l i) B (hb l i)
  have hi l := finite_sum_abs_bound (fun i => ∑ z, f l i z)
    ((Fintype.card ZeroWord : ℝ)*B) (fun i => hz l i)
  have hl := finite_sum_abs_bound (fun l => ∑ i, ∑ z, f l i z)
    ((Fintype.card (Fin 3) : ℝ)*((Fintype.card ZeroWord : ℝ)*B)) hi
  calc
    _ = 4*|∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, f l i z| := by
      rw [abs_mul]; norm_num
    _ ≤ 4*((Fintype.card (Fin 3) : ℝ)*
        ((Fintype.card (Fin 3) : ℝ)*((Fintype.card ZeroWord : ℝ)*B))) :=
      mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = _ := by simp only [quadRowMultiplier,Fintype.card_fin,Nat.cast_ofNat]; ring

private lemma rows_integral_bound (f : Fin 3 → Fin 3 → ZeroWord → R3 → ℝ)
    (B : ℝ) (hI : ∀ l i z, Integrable (f l i z))
    (hB : ∀ l i z, |∫ x, f l i z x| ≤ B) :
    Integrable (fun x => 4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, f l i z x) ∧
      |∫ x, 4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, f l i z x| ≤ quadRowMultiplier*B := by
  have hz l i := finite_integral_sum_bound (f l i) B (hI l i) (hB l i)
  have hi l := finite_integral_sum_bound (fun i x => ∑ z, f l i z x)
    ((Fintype.card ZeroWord : ℝ)*B) (fun i => (hz l i).1) (fun i => (hz l i).2)
  have hl := finite_integral_sum_bound (fun l x => ∑ i, ∑ z, f l i z x)
    ((Fintype.card (Fin 3) : ℝ)*((Fintype.card ZeroWord : ℝ)*B))
    (fun l => (hi l).1) (fun l => (hi l).2)
  refine ⟨hl.1.const_mul 4,?_⟩
  calc
    _ = 4*|∫ x, ∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, f l i z x| := by
      rw [integral_const_mul,abs_mul]; norm_num
    _ ≤ 4*((Fintype.card (Fin 3) : ℝ)*
        ((Fintype.card (Fin 3) : ℝ)*((Fintype.card ZeroWord : ℝ)*B))) :=
      mul_le_mul_of_nonneg_left hl.2 (by norm_num)
    _ = _ := by simp only [quadRowMultiplier,Fintype.card_fin,Nat.cast_ofNat]; ring

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

local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "TF" => referenceFirstHalf hO hD hF g L
local notation "TD" => referenceAdjointFirstHalf hO hD hF g L
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LD" => firstLinearZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "QD" => firstQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "D10" => originalFirstZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data


local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" d:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs d
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "SD" => actualWeightedSymmetricDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "ST" => originalQuadraticSymmetricTotal
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "GT" => originalQuadraticGainTotal
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "WG" => weightedOriginalTripleGain
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] firstQuadraticZeroCrossDensity finiteCoreReferenceProfileEnergy
  ActualHigherSFormation.higherSInput actualWeightedSymmetricDensity weightedOriginalTripleGain
  originalQuadraticSymmetricTotal originalQuadraticGainTotal referenceFirstHalf referenceAdjointFirstHalf

include hg in
private lemma original_first_physical_continuous (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD) :
    Continuous (fun x => KL (TF q (UF F) x)) ∧
      Continuous (fun x => KL (TD q (UF F) x)) := by
  have hFwd : (fun x => KL (TF q (UF F) x)) =
      (fun x => (nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x-
        (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x) := by
    funext x
    have h := nativeT_eq_first_and_original_zero hO hD hF g hg L q dr Ar p hdr hAr F x
    simpa only [ActualHigherSFormation.higherSInput] using eq_sub_of_add_eq h.symm
  have hRev : (fun x => KL (TD q (UF F) x)) =
      (fun x => (nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F).val x-
        (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x) := by
    funext x
    have h := nativeTdag_eq_first_and_original_zero hO hD hF g hg L q dr Ar p hdr hAr F x
    simpa only [ActualHigherSFormation.higherSInput] using eq_sub_of_add_eq h.symm
  constructor
  · rw [hFwd]
    exact (nativeT hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.sub
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous
  · rw [hRev]
    exact (nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.sub
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous


private lemma original_quadratic_weighted_integrable (dF : ℝ) (Cm : CRoom dF)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*QD g2 dr Ar p q F x) := by
  have hReg := actualZ2T2_contDiff_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm g2 hg2 dr Ar p hdr hAr q F hT
  have hFirst := original_first_physical_continuous hF hO hD g L hg q dr Ar p hdr hAr F
  have hCont : Continuous (QD g2 dr Ar p q F) := by
    unfold firstQuadraticZeroCrossDensity
    exact (continuous_const.mul (hFirst.1.inner ((KL).continuous.comp hReg.1.continuous))).sub
      (continuous_const.mul (hFirst.2.inner ((KL).continuous.comp hReg.2.1.continuous)))
  have hOff (x : R3) (hx : x ∉ tsupport F.val) : QD g2 dr Ar p q F x=0 := by
    have hZ : Z2 g2 dr Ar p q F x=0 := by
      by_contra hn
      exact hx (hReg.2.2.1 (subset_closure hn))
    have hR : T2 g2 dr Ar p q F x=0 := by
      by_contra hn
      exact hx (hReg.2.2.2 (subset_closure hn))
    simp only [firstQuadraticZeroCrossDensity,hZ,hR,map_zero,inner_zero_right,mul_zero,sub_self]
  have hMuCont : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hCompact : HasCompactSupport (fun x => referenceDensityFamily g L (q,x)*QD g2 dr Ar p q F x) :=
    HasCompactSupport.intro F.property.2.1 (by intro x hx; rw [hOff x hx,mul_zero])
  exact (hMuCont.mul hCont).integrable_of_hasCompactSupport hCompact

/-- Full literal original quadratic D10 integral, with original energy and all
profile/input-independent constants produced from the original data. -/
theorem exists_original_first_quadratic_zero_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cquad etaQuad : ℝ, 0 < Cquad ∧ 0 < etaQuad ∧ etaQuad ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaQuad →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*QD g2 dr Ar p q F x) ∧
        |∫ x, referenceDensityFamily g L (q,x)*QD g2 dr Ar p q F x| ≤
          Cquad*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  classical
  obtain ⟨dA,hdA,_hdδ,_hdδ0,_hdρ,_hΩ,⟨P⟩⟩ := exists_same_packet_allAngularAtom_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  let G := Classical.choice (exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel dA hdA)
  obtain ⟨Cgreen,etaGreen,hCgreen,heGreen,heGreen1,hGreen⟩ :=
    exists_actual_uniform_weighted_triple_symmetric_integral_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hdA P g2 hg2
  obtain ⟨Cgain,hCgain,hGain⟩ := exists_actual_uniform_weighted_triple_gain_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL P g2 hg2
  obtain ⟨Cr,hCr,hReference⟩ := exists_highInput_inclusion_reference_integral_bound
    hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  have hNpos : 0 < quadRowMultiplier := quadRowMultiplier_pos
  let Ctotal : ℝ := quadRowMultiplier*(Cgreen+Cgain)
  have hCtotal : 0 < Ctotal := mul_pos quadRowMultiplier_pos (add_pos hCgreen hCgain)
  refine ⟨Ctotal*Cr,min data.eta0 (min G.epsG etaGreen),mul_pos hCtotal hCr,
    lt_min data.eta0_pos (lt_min G.epsG_pos heGreen),min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have he0 : eta ≤ data.eta0 := he.trans (min_le_left _ _)
  have heG : eta ≤ G.epsG := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heGreen' : eta ≤ etaGreen := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  have he1 : eta ≤ 1 := he0.trans data.eta0_le
  have hMembers := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta heG K hK hKball F hsupp hb hs
  let U : R3 → Hi := UF F
  let beta := actualReferenceBeta g L q dr Ar p
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let e : R3 → ℝ := fun x => inclusionEnergyDensity IH (beta x) U x
  have hMuCont : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hMu (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
  have hBetaCont : Continuous beta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hBetaPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hUSmooth : ContDiff ℝ ∞ U := by
    dsimp only [U]
    unfold ActualHigherSFormation.higherSInput
    exact contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hUOff (x : R3) (hx : x ∉ tsupport F.val) : U x=0 := highInput_eq_zero_off hO hD F x hx
  have hEI : Integrable (fun x => mu x*e x) :=
    inclusionEnergy_integrable IH mu beta U (tsupport F.val) F.property.2.1
      hMuCont hBetaCont (fun x => (hBetaPos x).ne') hUSmooth hUOff
  have hMCont : Continuous (fun x => mu x*beta x*‖U x‖^2) :=
    (hMuCont.mul hBetaCont).mul (hUSmooth.continuous.norm.pow 2)
  have hMCompact : HasCompactSupport (fun x => mu x*beta x*‖U x‖^2) :=
    HasCompactSupport.intro F.property.2.1 (by intro x hx; simp only [hUOff x hx,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero])
  have hMI : Integrable (fun x => mu x*beta x*‖U x‖^2) :=
    hMCont.integrable_of_hasCompactSupport hMCompact
  have hMassPoint (x : R3) : beta x*‖U x‖^2 ≤ e x := by
    have hd : 0 ≤ (beta x)⁻¹*(∑ i : Fin 3, ‖IH (directionalFDeriv (coordinateDirection i) U x)‖^2) :=
      mul_nonneg (inv_nonneg.mpr (hBetaPos x).le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    dsimp only [e,inclusionEnergyDensity]
    linarith only [hd]
  have hMassComp : (∫ x, mu x*beta x*‖U x‖^2) ≤ ∫ x, mu x*e x :=
    integral_mono hMI hEI (fun x => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hMassPoint x) (hMu x))
  have hPhysicalI := original_quadratic_weighted_integrable
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    G.commonRadius G.common g2 hg2 q dr Ar p hdr hAr F hMembers.2
  have hSplit := original_quadratic_weighted_split
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P G.commonRadius G.common g2 hg2 q dr Ar p hdr hAr F hMembers.1 hMembers.2
  have hEach (i l : Fin 3) (z : ZeroWord) := hGreen q hq dr hdr hdr1 Ar hAr p hp eta heta heGreen'
    K hK hKball F hsupp hb hs i l z (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2
  have hS := rows_integral_bound
    (fun l i z => SD g2 q dr Ar p F i l z (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2)
    (Cgreen*eta*(∫ x, mu x*beta x*‖U x‖^2))
    (fun l i z => (hEach i l z).1) (fun l i z => (hEach i l z).2)
  have hSI : Integrable (ST g2 q dr Ar p F) := by
    unfold originalQuadraticSymmetricTotal
    exact hS.1
  have hGainEq : GT P g2 q dr Ar p F=
      (fun x => ST g2 q dr Ar p F x-mu x*QD g2 dr Ar p q F x) := by
    funext x
    have h := hSplit x
    linarith only [h]
  have hGI : Integrable (GT P g2 q dr Ar p F) := hGainEq.symm ▸ hSI.sub hPhysicalI
  have hPoint (x : R3) : |GT P g2 q dr Ar p F x| ≤
      (quadRowMultiplier*Cgain*eta)*(mu x*e x) := by
    by_cases hx : x ∈ tsupport F.val
    · have hRows (l i : Fin 3) (z : ZeroWord) :
          |mu x*WG P g2 q dr Ar p U i l z x| ≤ mu x*(Cgain*eta*e x) := by
        rw [abs_mul,abs_of_nonneg (hMu x)]
        exact mul_le_mul_of_nonneg_left
          (hGain q hq dr hdr hdr1 Ar hAr p hp eta heta he1 x
            (ball_subset_closedBall (hKball (hsupp hx))) (hb x (hsupp hx)) (hs x (hsupp hx))
            (hMembers.1 x hx) U i l z) (hMu x)
      have hSum := rows_abs_bound (fun l i z => mu x*WG P g2 q dr Ar p U i l z x)
        (mu x*(Cgain*eta*e x)) hRows
      unfold originalQuadraticGainTotal
      exact hSum.trans_eq (by ring)
    · have hG0 (l i : Fin 3) (z : ZeroWord) : WG P g2 q dr Ar p U i l z x=0 := by
        simp only [weightedOriginalTripleGain,hUOff x hx,map_zero,zero_apply,mul_zero,add_zero]
      dsimp only [U] at hG0
      have hGT0 : GT P g2 q dr Ar p F x=0 := by
        simp only [originalQuadraticGainTotal,hG0,mul_zero,Finset.sum_const_zero]
      rw [hGT0,abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (hMu x)
        (inclusionEnergyDensity_nonneg IH (beta x) U x (hBetaPos x).le))
  have hNormPoint (x : R3) : ‖GT P g2 q dr Ar p F x‖ ≤
      (quadRowMultiplier*Cgain*eta)*(mu x*e x) := by
    simpa only [Real.norm_eq_abs] using hPoint x
  have hGMono := integral_mono hGI.norm (hEI.const_mul (quadRowMultiplier*Cgain*eta)) hNormPoint
  rw [integral_const_mul] at hGMono
  have hNormInt : |∫ x, GT P g2 q dr Ar p F x| ≤ ∫ x, ‖GT P g2 q dr Ar p F x‖ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (GT P g2 q dr Ar p F)
  have hGBound : |∫ x, GT P g2 q dr Ar p F x| ≤
      (quadRowMultiplier*Cgain*eta)*(∫ x, mu x*e x) := hNormInt.trans hGMono
  have hSraw : |∫ x, ST g2 q dr Ar p F x| ≤
      quadRowMultiplier*(Cgreen*eta*(∫ x, mu x*beta x*‖U x‖^2)) := by
    unfold originalQuadraticSymmetricTotal
    exact hS.2
  have hSBound : |∫ x, ST g2 q dr Ar p F x| ≤
      (quadRowMultiplier*Cgreen*eta)*(∫ x, mu x*e x) := by
    calc
      _ ≤ quadRowMultiplier*(Cgreen*eta*(∫ x, mu x*beta x*‖U x‖^2)) := hSraw
      _ = (quadRowMultiplier*Cgreen*eta)*(∫ x, mu x*beta x*‖U x‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hMassComp (by positivity)
  have hEq : (fun x => mu x*QD g2 dr Ar p q F x)=
      (fun x => ST g2 q dr Ar p F x-GT P g2 q dr Ar p F x) := funext hSplit
  have hBound : |∫ x, mu x*QD g2 dr Ar p q F x| ≤ Ctotal*eta*(∫ x, mu x*e x) := by
    rw [hEq,integral_sub hSI hGI]
    exact ((abs_sub _ _).trans (add_le_add hSBound hGBound)).trans_eq (by dsimp only [Ctotal]; ring)
  have hFclosed : tsupport F.val ⊆ closedBall y0 ρ := hsupp.trans (hKball.trans ball_subset_closedBall)
  have hRef := hReference q hq dr Ar p hdr hAr hp F hFclosed (fun x hx => hb x (hsupp hx))
  refine ⟨hPhysicalI,?_⟩
  exact hBound.trans ((mul_le_mul_of_nonneg_left hRef (mul_nonneg hCtotal.le heta)).trans_eq (by ring))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticOriginalIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticOriginalIntegral.exists_original_first_quadratic_zero_integral_bound
