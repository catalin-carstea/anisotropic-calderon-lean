import Calderon.ActualFullEGainedHighCore

/-! All maps below use the actual retained coefficient germs. This file assembles the
full E/E high graph, the smooth paired low endpoint, and finite joint jet caps. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def fullHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] fullHighNormed
@[instance_reducible] private def fullHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] fullHighSpace
@[instance_reducible] private def fullLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] fullLowNormed
@[instance_reducible] private def fullLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] fullLowSpace
@[instance_reducible] private def fullNegativeNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] fullNegativeNormed
@[instance_reducible] private def fullNegativeSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] fullNegativeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RH" => radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HR" => angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The swapped gained pairing, through the explicit ordinary endpoint wrappers.
These transports keep the same W and the genuine ordered reverse. -/
theorem full_gained_swapped_pairing
    (hreg : FixedDirichletRegularity)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half) (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hGraph : ∀ k l : Fin 3, ∀ u : Hi,
      JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W k l t u) =
        orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 k t (EH l t u)-
          EL l t (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 k t u))
    (u v : Hi) :
    PP (IH v) (JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t u)) =
      PP (IH u) (JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W j i t v)) := by
  let eH := orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  let eL := orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  have hForwardCompat (k : Fin 3) (z : Hi) : JL (EH k t z)=EL k t (IH z) := by
    have hp := (W.piGerm k t ht).self_of_nhds
    exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg k t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W k t)
      hp.1 hp.2.1 z
  have hReverseCompat (k : Fin 3) (z : Hi) : JL (eH k t z)=eL k t (IH z) := by
    have hp := (W.piGerm k t ht).self_of_nhds
    simpa only [eH,eL,orderedReverseHigh,orderedReverseLow,originalRadialReverseHigh,
      originalRadialReverseLow,jacobiAngularReverseHigh,jacobiAngularReverseLow] using
      explicit_ordered_reverse_high_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        k t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W k t)
        hp.2.1 hp.2.2 z
  have hPivot (k : Fin 3) (x y : Half) : PP x (EL k t y)=PP y (eL k t x) := by
    have hp := (W.piGerm k t ht).self_of_nhds
    simpa only [eL,orderedReverseLow,originalRadialReverseLow,jacobiAngularReverseLow] using
      canonicalLow_explicit_ordered_reverse_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        k t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W k t)
        hp.2.1 hp.2.2 x y
  have hForward (k : Fin 3) (z : Hi) (x : Half) :
      PP (IH z) (EL k t x)=PP x (JL (eH k t z)) :=
    (hPivot k (IH z) x).trans (congrArg (PP x) (hReverseCompat k z).symm)
  have hReverse (k : Fin 3) (z : Hi) (x : Half) :
      PP (IH z) (eL k t x)=PP x (JL (EH k t z)) :=
    (hPivot k x (IH z)).symm.trans (congrArg (PP x) (hForwardCompat k z).symm)
  have h1 : PP (IH v) (eL i t (EH j t u))=PP (IH u) (eL j t (EH i t v)) :=
    (hReverse i v (EH j t u)).trans
      ((v016_pairing_inclusion_symm (EH j t u) (EH i t v)).trans
        (hReverse j u (EH i t v)).symm)
  have h2 : PP (IH v) (EL j t (eH i t u))=PP (IH u) (EL i t (eH j t v)) :=
    (hForward j v (eH i t u)).trans
      ((v016_pairing_inclusion_symm (eH i t u) (eH j t v)).trans
        (hForward i u (eH j t v)).symm)
  have hc := (congrArg (fun z : Neg => PP (IH v) z) (hGraph i j u)).trans
    (v016_pairing_sub_right (IH v) _ _)
  have hd := (congrArg (fun z : Neg => PP (IH u) z) (hGraph j i v)).trans
    (v016_pairing_sub_right (IH u) _ _)
  exact hc.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hd.symm)

private theorem fullBalancedLow_exists (Ch Dh : Hi →L[ℝ] Half)
    (hAdj : ∀ u v : Hi, PP (IH v) (JL (Ch u))=PP (IH u) (JL (Dh v))) :
    ∃ B : Half →L[ℝ] Neg,
      B.comp IH=(JL).comp Ch ∧
      (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp B=
        (v016TransposeL Dh).comp JL ∧
      ‖B‖ ≤ (‖Dh‖+‖Ch‖)/2 := by
  have hc := v016_compatible_of_adjunction Ch Dh hAdj
  let B : Half →L[ℝ] Neg := sphereSobolevBalancedDualEndpointL (v016TransposeL Dh) Ch hc
  have hUp : B.comp IH=(JL).comp Ch :=
    sphereSobolevBalancedDualEndpointL_upper_inclusion (v016TransposeL Dh) Ch hc
  have hLo : (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp B=
      (v016TransposeL Dh).comp JL :=
    sphereSobolevBalancedDualEndpointL_lower_inclusion (v016TransposeL Dh) Ch hc
  have hN : ‖B‖ ≤ (‖v016TransposeL Dh‖+‖Ch‖)/2 :=
    norm_sphereSobolevBalancedDualEndpointL_le (v016TransposeL Dh) Ch hc
  have hNT := norm_v016TransposeL_apply_le Dh
  exact ⟨B,hUp,hLo,hN.trans (by linarith)⟩

/-- Actual full high/low E/E weak endpoint family, using the actual paired/balanced
construction on the same W. -/
theorem exists_commonRoom_fullGained_paired_endpoints
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    ∃ Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
      ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        (∀ u : Hi,
          JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t u) =
            orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t (EH j t u)-
              EL j t (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t u)) ∧
        (Cl i j t).comp IH=(JL).comp
          (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j t)=
          (v016TransposeL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W j i t)).comp JL ∧
        ‖Cl i j t‖ ≤
          (‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W j i t‖+
           ‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t‖)/2 := by
  classical
  let highWitnesses := exists_commonRoom_fullGainedHigh_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel δ0 hδ0 W
  let δ : ℝ := Classical.choose highWitnesses
  have highFacts := Classical.choose_spec highWitnesses
  have hδ : 0 < δ := highFacts.1
  have hδ0le : δ ≤ δ0 := highFacts.2.1
  have hδρ : δ ≤ ρ := highFacts.2.2.1
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := highFacts.2.2.2.1
  let Gcoord := Classical.choose highFacts.2.2.2.2
  have coordFacts := Classical.choose_spec highFacts.2.2.2.2
  let GN := Classical.choose coordFacts
  have hGraph := Classical.choose_spec coordFacts
  let Ch := fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W
  have hSub := commonRoom_mono y0 ρ hδ0le
  have hLow (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ∃ B : Half →L[ℝ] Neg, B.comp IH=(JL).comp (Ch i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp B=
          (v016TransposeL (Ch j i t)).comp JL ∧ ‖B‖ ≤ (‖Ch j i t‖+‖Ch i j t‖)/2 := by
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
    have hAdj : ∀ u v : Hi, PP (IH v) (JL (Ch i j t u))=PP (IH u) (JL (Ch j i t v)) :=
      full_gained_swapped_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
        hreg Gcoord GN δ0 W i j t ⟨hSub ht.1,ht.2⟩ hSeg (fun k l => hGraph k l t ht)
    exact fullBalancedLow_exists (Ch i j t) (Ch j i t) hAdj
  let Cl (i j : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
    if ht : t ∈ ParamRoom δ then Classical.choose (hLow i j t ht) else 0
  refine ⟨δ,hδ,hδ0le,hδρ,Gcoord,GN,Cl,?_⟩
  intro i j t ht
  have hAt := Classical.choose_spec (hLow i j t ht)
  have hCl : Cl i j t=Classical.choose (hLow i j t ht) := dif_pos ht
  exact ⟨hGraph i j t ht,by simpa only [hCl] using hAt⟩


/- The ordinary K/Z smoothness proof belongs to the importing final assembly module. -/
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
