import Calderon.ActualMixedAngularPairedGains
import Calderon.ActualHighSmoothMultiplierFixedTopology

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualMixedCanonicalMultiplierGains
  ActualRetainedGeneratorMultiplierGains ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualCanonicalAngularGainedBracket NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TH" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "TL" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SH" => referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "SL" => referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "LH" => loweringMultiplierHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "RA" => raisingMultiplierHalf hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CS" => raisingAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "KK" => gainedAtOrder hF hO hD (3/2 : ℝ)
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "ΩH" => referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc
open ActualGeneratorRadialGainedRows
attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringMultiplierHigh raisingMultiplierHalf
  loweringEHigh raisingReverseHigh


/-- Genuine Hi-to-Hi sharp multiplier Taylor regularity on the open high locus. -/
lemma highSharpMultiplierSecondRemainder_contDiffAt_of_high_segment
    (Q : SmoothCoefficientJets 3) (p : Pphys)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ ΩH) :
    ContDiffAt ℝ ∞ (fun z : Pphys => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q z.1 z.2.1 z.2.2) p := by
  unfold referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  let T : ((ℝ × R3) × ℝ) → Pphys := fun z => (z.1.1,(z.1.2,z.2))
  let σ : Pphys → (ℝ × R3) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  let U : Set ((ℝ × R3) × ℝ) := T ⁻¹' ΩH
  let F : ((ℝ × R3) × ℝ) → Hi →L[ℝ] Hi := fun z =>
    referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (T z)
  have hT : ContDiff ℝ ∞ T := contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hU : IsOpen U := (isOpen_referenceGaugeNormalHighInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc).preimage hT.continuous
  have hFs : ContDiffOn ℝ ∞ F U := by
    intro z hz
    exact ((contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (T z) hz.1 hz.2).comp
        z hT.contDiffAt).contDiffWithinAt
  have hTaylor := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    F U hU hFs (p.1,p.2.1) p.2.2 hHigh
  simpa only [F,T,σ,Function.comp_def] using hTaylor.comp (f := σ) p hσ.contDiffAt

/-- Full CAS regularity; coordinate, rotation and physical degree words all remain. -/
lemma raisingSharpAngular_contDiffAt_of_segments (hreg : FixedDirichletRegularity)
    (i : Fin 3) (p : Pphys)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ ΩH)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun z : Pphys => CS hreg i z.1 z.2.1 z.2.2) p := by
  have hG (k : Fin 3) := highSharpMultiplierSecondRemainder_contDiffAt_of_high_segment
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData (coordinateJets k) p hHigh
  have hR (k : Fin 3) : ContDiffAt ℝ ∞ (fun z : Pphys => referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k i z.1 z.2.1 z.2.2) p := by
    exact contDiffAt_sharpRotationGain hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData k i p hSeg
  have hB : ContDiffAt ℝ ∞ (fun z : Pphys => referenceRadialDegreeCommutatorGainedHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 z.1 z.2.1 z.2.2) p := by
    exact contDiffAt_referenceRadialDegreeCommutatorGainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg
  unfold raisingAngularHighCommutator
  exact ((ContDiffAt.sum (fun k _ => (contDiffAt_const.clm_comp (hG k)).sub
    ((hR k).clm_comp contDiffAt_const))).sub (contDiffAt_const.clm_comp (hG i))).add
      (hB.clm_comp contDiffAt_const)

/-- Original data provide the high and weak radial segment conditions before all inputs. -/
theorem exists_commonRoom_raisingSharpAngular_regular (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (hδ0 : 0 < δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ i : Fin 3, ∀ p ∈ commonRoom y0 ρ δ,
        ContDiffAt ℝ ∞ (fun z : Pphys => CS hreg i z.1 z.2.1 z.2.2) p := by
  obtain ⟨lam,Lam,dF,_hlam,hdF,hdFρ,hFinite⟩ :=
    exists_reference_commonRadius_finitePhysicalDomain_room
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  obtain ⟨dO,hdO,_hdOρ,hΩ⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let δ : ℝ := min δ0 (min dF dO)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdF hdO)
  have hδF : δ ≤ dF := (min_le_right _ _).trans (min_le_left _ _)
  have hδO : δ ≤ dO := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,min_le_left _ _,hδF.trans hdFρ,?_⟩
  intro i p hp
  apply raisingSharpAngular_contDiffAt_of_segments hF hO hD hcalc τ0
    g L y0 Φ B ε C ρ H a w hData hreg i p
  · intro θ hθ
    have hr : |θ*p.2.2| ≤ dF := by
      rw [abs_mul,abs_of_nonneg hθ.1]
      exact (mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)).trans
        ((one_mul _).le.trans ((abs_le.mpr hp.2.2).trans hδF))
    have hz := hFinite (p.1,(p.2.1,θ*p.2.2)) ⟨hp.1,hp.2.1,abs_le.mp hr⟩
    exact hz.2.2.2.1
  · exact segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      hΩ p (commonRoom_mono y0 ρ hδO hp)

/-- Ambient smooth germs of every coefficient and all four original zero words, for ANY caller W. -/
lemma mixed_coefficients_zeroWords_contDiffAt (δ0 : ℝ) (W : CoeffRoom δ0)
    (t : Tpar) (ht : t ∈ ParamRoom δ0) (j : Fin 3) :
    ContDiffAt ℝ ∞ (PiH j) t ∧ ContDiffAt ℝ ∞ (PiL j) t ∧
    (∀ m : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NH (NJ3 j m z.1)) t ∧
      ContDiffAt ℝ ∞ (fun z : Tpar => NL (NJ2 j m z.1)) t) ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => ZH j z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => ZL j z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => zH j z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => zL j z.1) t := by
  have hPS := ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt
    hcalc hF hO hD τ0 (W.piScalar j) (W.piSmooth j)
      W.piSupport W.piCompact (W.piZero j) t
  have hp := W.piGerm j t ht
  have hPH : ContDiffAt ℝ ∞ (PiH j) t :=
    hPS.1.congr_of_eventuallyEq (hp.mono (fun z hz => hz.1.symm))
  have hPL : ContDiffAt ℝ ∞ (PiL j) t :=
    hPS.2.1.congr_of_eventuallyEq (hp.mono (fun z hz => hz.2.1.symm))
  have hN (m : Fin 3) : ContDiffAt ℝ ∞ (fun z : Tpar => NH (NJ3 j m z.1)) t ∧
      ContDiffAt ℝ ∞ (fun z : Tpar => NL (NJ2 j m z.1)) t := by
    have hs := ActualFullEZeroRowsSmoothGerms.commonSupport_native_contDiffAt
      hcalc hF hO hD τ0 (W.jacobiScalar j m) (W.jacobiSmooth j m)
      (W.jacobiSupport j m) (W.jacobiCompact j m) (W.jacobiZero j m) t.1
    have hn := W.jacobiGerm j m t.1 ht.1
    have hNH : ContDiffAt ℝ ∞ (fun z : Pphys => NH (NJ3 j m z)) t.1 :=
      hs.1.congr_of_eventuallyEq (hn.mono (fun z hz => hz.1.symm))
    have hNL : ContDiffAt ℝ ∞ (fun z : Pphys => NL (NJ2 j m z)) t.1 :=
      hs.2.1.congr_of_eventuallyEq (hn.mono (fun z hz => hz.2.1.symm))
    exact ⟨hNH.comp t contDiffAt_fst,hNL.comp t contDiffAt_fst⟩
  have hProj : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDadj (s : ℝ) :=
    ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffAt (x := t)
  have hDfwd (s : ℝ) :=
    ((contDiff_reference_sphereSobolevRadialDriftL g hg L hF hO hD s).comp hProj).contDiffAt (x := t)
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiffAt_fst.snd.snd
  refine ⟨hPH,hPL,hN,?_,?_,?_,?_⟩
  · unfold zeroCorrectionHigh
    exact hr.smul (ContDiffAt.sum (fun m _ => (hDadj (3/2 : ℝ)).clm_comp
      (contDiffAt_const.clm_comp (hN m).1)))
  · unfold zeroCorrectionHalf
    exact hr.smul (ContDiffAt.sum (fun m _ => (hDadj (1/2 : ℝ)).clm_comp
      (contDiffAt_const.clm_comp (hN m).2)))
  · unfold zeroReverseHigh
    exact hr.smul (ContDiffAt.sum (fun m _ => (hN m).1.clm_comp
      (contDiffAt_const.clm_comp (hDfwd (3/2 : ℝ)))))
  · unfold zeroReverseHalf
    exact hr.smul (ContDiffAt.sum (fun m _ => (hN m).2.clm_comp
      (contDiffAt_const.clm_comp (hDfwd (1/2 : ℝ)))))

/-- Internal finite-word regularity transport. Every premise is discharged by actual room producers below. -/
lemma mixed_high_contDiffOn_of_actual_factors (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (hδ0le : δ ≤ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω) (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (hCT : ∀ i : Fin 3, ContDiffOn ℝ ∞ (CT hreg G i) (commonRoom y0 ρ δ))
    (hM : ∀ i : Fin 3, ∀ c : RetainedCoefficient,
      ContDiffOn ℝ ∞ (LH δ0 W i c) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (RA δ0 W i c) (ParamRoom δ))
    (hCS : ∀ i : Fin 3, ∀ p ∈ commonRoom y0 ρ δ,
      ContDiffAt ℝ ∞ (fun z : Pphys => CS hreg i z.1 z.2.1 z.2.2) p) :
    ∀ i j : Fin 3, ContDiffOn ℝ ∞ (CH hreg G δ0 W i j) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (HH hreg δ0 W i j) (ParamRoom δ) := by
  have hSub0 := commonRoom_mono y0 ρ hδ0le
  have hCoe (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    mixed_coefficients_zeroWords_contDiffAt hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      δ0 W t ⟨hSub0 ht.1,ht.2⟩ j
  have hPiH (j : Fin 3) : ContDiffOn ℝ ∞ (PiH j) (ParamRoom δ) :=
    fun t ht => (hCoe j t ht).1.contDiffWithinAt
  have hPiL (j : Fin 3) : ContDiffOn ℝ ∞ (PiL j) (ParamRoom δ) :=
    fun t ht => (hCoe j t ht).2.1.contDiffWithinAt
  have hNH (j m : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => NH (NJ3 j m z.1)) (ParamRoom δ) :=
    fun t ht => ((hCoe j t ht).2.2.1 m).1.contDiffWithinAt
  have hNL (j m : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => NL (NJ2 j m z.1)) (ParamRoom δ) :=
    fun t ht => ((hCoe j t ht).2.2.1 m).2.contDiffWithinAt
  have hZH (j : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => ZH j z.1) (ParamRoom δ) :=
    fun t ht => (hCoe j t ht).2.2.2.1.contDiffWithinAt
  have hZL (j : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => ZL j z.1) (ParamRoom δ) :=
    fun t ht => (hCoe j t ht).2.2.2.2.1.contDiffWithinAt
  have hzH (j : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => zH j z.1) (ParamRoom δ) :=
    fun t ht => (hCoe j t ht).2.2.2.2.2.1.contDiffWithinAt
  have hzL (j : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => zL j z.1) (ParamRoom δ) :=
    fun t ht => (hCoe j t ht).2.2.2.2.2.2.contDiffWithinAt
  have hRad (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    contDiffAt_actualAngularRadialRemainder_families_of_segment hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hreg t.1
      (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
  have hTH : ContDiffOn ℝ ∞ (fun t : Tpar => TH t.1) (ParamRoom δ) := fun t ht =>
    ((hRad t ht).1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hSH : ContDiffOn ℝ ∞ (fun t : Tpar => SH t.1.1 t.1.2.1 t.1.2.2) (ParamRoom δ) := by
    intro t ht
    have he := ((hRad t ht).2.2.1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt (s := ParamRoom δ)
    have hFun : (sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData ∘
        (Prod.fst : Tpar → Pphys)) = (fun z : Tpar => SH z.1.1 z.1.2.1 z.1.2.2) := by
      funext z
      rfl
    rw [hFun] at he
    exact he
  have hCTp (i : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar => CT hreg G i t.1) (ParamRoom δ) :=
    (hCT i).comp contDiff_fst.contDiffOn (fun t ht => ht.1)
  have hCSp (i : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar => CS hreg i t.1.1 t.1.2.1 t.1.2.2) (ParamRoom δ) :=
    fun t ht => ((hCS i t.1 ht.1).comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  intro i j
  refine ⟨?_,?_⟩
  · unfold loweringEHigh
    have hR := ((hCTp i).clm_comp (hPiH j)).add (hTH.clm_comp (hM i (Sum.inl j)).1)
    have hA := ContDiffOn.sum (s := (Finset.univ : Finset (Fin 3))) (fun m _ => ((contDiffOn_const (c := KK i m)).clm_comp (hNH j m)).add
      ((contDiffOn_const (c := AH m)).clm_comp (hM i (Sum.inr (j,m))).1))
    exact ((hR.add hA).add (contDiffOn_const.clm_comp (hZH j))).sub
      ((hZL j).clm_comp contDiffOn_const)
  · unfold raisingReverseHigh
    have hR := ((hM i (Sum.inl j)).2.clm_comp hSH).add ((hPiL j).clm_comp (hCSp i))
    have hA := ContDiffOn.sum (s := (Finset.univ : Finset (Fin 3))) (fun m _ => ((hM i (Sum.inr (j,m))).2.clm_comp (contDiffOn_const (c := aH m))).sub
      ((hNL j m).clm_comp (contDiffOn_const (c := KK m i))))
    exact ((hR.add hA).add (contDiffOn_const.clm_comp (hzH j))).sub
      ((hzL j).clm_comp contDiffOn_const)

private lemma use_lowering_native {D V I : Type*}
    {A B C : D → Prop} {P Q : D → V → Prop} {R S T : D → V → I → Prop} {Result : Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ v : V,
      P d v ∧ Q d v ∧ ∀ i, R d v i ∧ S d v i ∧ T d v i)
    (use : ∀ d v, A d → B d → C d → (∀ i, R d v i) → (∀ i, S d v i) → Result) : Result := by
  rcases h with ⟨d,ha,hb,hc,v,_hp,_hq,hrs⟩
  exact use d v ha hb hc (fun i => (hrs i).1) (fun i => (hrs i).2.1)

private lemma use_mixed_native {D K : Type*}
    {A B C S G : D → Prop} {P N : D → K → Prop} {Result : Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ k : K, P d k ∧ S d ∧ G d ∧ N d k)
    (use : ∀ d, A d → S d → G d → Result) : Result := by
  rcases h with ⟨d,ha,_hb,_hc,_k,_hp,hs,hg,_hn⟩
  exact use d ha hs hg

private lemma use_radius_data {D : Type*} {A B C P : D → Prop} {Result : Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ P d)
    (use : ∀ d, A d → P d → Result) : Result := by
  rcases h with ⟨d,ha,_hb,_hc,hp⟩
  exact use d ha hp

private lemma use_mixed_graphs {D V : Type*} {A B C O : D → Prop}
    {P : D → V → Prop} {Result : Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ O d ∧ ∃ v : V, P d v)
    (use : ∀ d v, A d → P d v → Result) : Result := by
  rcases h with ⟨d,ha,_hb,_hc,_ho,v,hp⟩
  exact use d v ha hp

private lemma reindex_pair_caps {I J : Type} {P : I × J → ℝ → Prop}
    (h : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : I × J, P z M) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : I, ∀ j : J, P (i,j) M := by
  rcases h with ⟨M,hM,hP⟩
  exact ⟨M,hM,fun i j => hP (i,j)⟩

private lemma uniform_mixed_jet_caps {I X V Z : Type} [Fintype I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (K : Set X) (hK : IsCompact K) (hU : UniqueDiffOn ℝ K)
    (f g : I → X → V) (b : I → X → Z)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) K) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) K)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ n : ℕ, n ≤ N → ∀ t ∈ K,
      ‖iteratedFDerivWithin ℝ n (f i) K t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (g i) K t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (b i) K t‖ ≤ M := by
  classical
  choose Cf hCf using fun i : I => exists_compact_iteratedFDerivWithin_bound (f i) K hK hU (hf i) N
  choose Cg hCg using fun i : I => exists_compact_iteratedFDerivWithin_bound (g i) K hK hU (hg i) N
  choose Cb hCb using fun i : I => exists_compact_iteratedFDerivWithin_bound (b i) K hK hU (hb i) N
  let M : ℝ := ∑ i : I, (Cf i+Cg i+Cb i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => add_nonneg
    (add_nonneg (hCf i).1 (hCg i).1) (hCb i).1)
  refine ⟨M,hM0,?_⟩
  intro i n hn t ht
  have hOne : Cf i+Cg i+Cb i ≤ M := Finset.single_le_sum
    (fun k _ => add_nonneg (add_nonneg (hCf k).1 (hCg k).1) (hCb k).1) (Finset.mem_univ i)
  have hF0 := (hCf i).1
  have hG0 := (hCg i).1
  have hB0 := (hCb i).1
  exact ⟨((hCf i).2 n hn t ht).trans (by linarith),
    ((hCg i).2 n hn t ht).trans (by linarith),
    ((hCb i).2 n hn t ht).trans (by linarith)⟩

/-- Actual smooth mixed endpoint producer, with all finite joint jet caps on the same original W.
The radius precedes every jet budget and every later physical profile. -/
theorem exists_commonRoom_actual_mixedAngular_smooth_caps
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      ∃ Bl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
        (∀ i j : Fin 3,
          ContDiffOn ℝ ∞ (CH hreg G δ0 W i j) (ParamRoom δ) ∧
          ContDiffOn ℝ ∞ (HH hreg δ0 W i j) (ParamRoom δ) ∧
          ContDiffOn ℝ ∞ (Bl i j) (ParamRoom δ)) ∧
        (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
          (∀ u : Hi, JL (CH hreg G δ0 W i j t u)=aL i (EH j t u)-EL j t (aH i u)) ∧
          (∀ u : Hi, JL (HH hreg δ0 W i j t u)=AL i (eH j t u)-eL j t (AH i u)) ∧
          (Bl i j t).comp IH=(JL).comp (CH hreg G δ0 W i j t) ∧
          (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Bl i j t)=
            (v016TransposeL (-(HH hreg δ0 W i j t))).comp JL) ∧
        (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (CH hreg G δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (HH hreg δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Bl i j) (ParamRoom δ) t‖ ≤ M) := by
  classical
  apply use_lowering_native
    (exists_reference_commonRadius_loweringAngularHigh_graph_caps
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel)
  intro dT G hdT hdTρ hΩT hCTGraph hCTS
  apply use_mixed_native
    (exists_commonRoom_actual_mixed_multiplier_gains
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel δ0 hδ0 W)
  intro dM hdM hMS hMG
  apply use_radius_data
    (exists_commonRoom_raisingSharpAngular_regular
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hreg δ0 hδ0)
  intro dS hdS hCSAt
  apply use_mixed_graphs
    (exists_commonRoom_actual_mixedAngular_high_graphs
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg hKernel δ0 hδ0 W)
  intro dH _Gignored hdH hHGraph
  let δ : ℝ := min δ0 (min dT (min dM (min dS dH)))
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdT (lt_min hdM (lt_min hdS hdH)))
  have hδ0le : δ ≤ δ0 := min_le_left _ _
  have hδT : δ ≤ dT := (min_le_right _ _).trans (min_le_left _ _)
  have hδM : δ ≤ dM := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδS : δ ≤ dS := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδH : δ ≤ dH := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hSub0 := commonRoom_mono y0 ρ hδ0le
  have hSubT := commonRoom_mono y0 ρ hδT
  have hSubM := commonRoom_mono y0 ρ hδM
  have hSubS := commonRoom_mono y0 ρ hδS
  have hSubH := commonRoom_mono y0 ρ hδH
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := fun p hp => hΩT (hSubT hp)
  let Cf := CH hreg G δ0 W
  let Hf := HH hreg δ0 W
  have hSmooth (i j : Fin 3) : ContDiffOn ℝ ∞ (Cf i j) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (Hf i j) (ParamRoom δ) :=
    mixed_high_contDiffOn_of_actual_factors hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W δ hδ0le hRoom G
      (fun i => (hCTS i).mono hSubT)
      (fun i c => ⟨((hMS i c).1.mono (fun t ht => ⟨hSubM ht.1,ht.2⟩)),
        ((hMS i c).2.mono (fun t ht => ⟨hSubM ht.1,ht.2⟩))⟩)
      (fun i p hp => hCSAt i p (hSubS hp)) i j
  have hGraphs (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      (∀ u : Hi, JL (Cf i j t u)=aL i (EH j t u)-EL j t (aH i u)) ∧
      (∀ u : Hi, JL (Hf i j t u)=AL i (eH j t u)-eL j t (AH i u)) := by
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
    exact ⟨loweringEHigh_graph_of_actual_words hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg G δ0 W i j t ⟨hSub0 ht.1,ht.2⟩ hSeg
        (hCTGraph i t.1 (hSubT ht.1)) (fun c => (hMG i c t ⟨hSubM ht.1,ht.2⟩).1),
      (hHGraph i j t ⟨hSubH ht.1,ht.2⟩).2⟩
  have hAdj (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v : Hi) :
      PP (IH v) (JL (Cf i j t u))=PP (IH u) (JL ((-(Hf i j t)) v)) :=
    mixed_high_pairing_of_graphs hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W i j t ⟨hSub0 ht.1,ht.2⟩
      (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
      (Cf i j t) (Hf i j t) (hGraphs i j t ht).1 (hGraphs i j t ht).2 u v
  have hK : IsCompact (ParamRoom δ) := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hLow (i j : Fin 3) := v016_exists_contDiffOn_lowEndpoint (ParamRoom δ) hU
    (Cf i j) (fun t => -(Hf i j t)) (hSmooth i j).1 (hSmooth i j).2.neg (hAdj i j)
  choose Bl hBl using hLow
  refine ⟨δ,hδ,hδ0le,hδT.trans hdTρ,G,Bl,?_,?_,?_⟩
  · exact fun i j => ⟨(hSmooth i j).1,(hSmooth i j).2,(hBl i j).1⟩
  · intro i j t ht
    exact ⟨(hGraphs i j t ht).1,(hGraphs i j t ht).2,
      ((hBl i j).2 t ht).1,((hBl i j).2 t ht).2.1⟩
  · intro N
    exact reindex_pair_caps (uniform_mixed_jet_caps (ParamRoom δ) hK hU
      (fun z : Fin 3 × Fin 3 => Cf z.1 z.2) (fun z : Fin 3 × Fin 3 => Hf z.1 z.2)
      (fun z : Fin 3 × Fin 3 => Bl z.1 z.2)
      (fun z => (hSmooth z.1 z.2).1) (fun z => (hSmooth z.1 z.2).2)
      (fun z => (hBl z.1 z.2).1) N)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
