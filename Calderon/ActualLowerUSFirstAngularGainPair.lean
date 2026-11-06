import Calderon.ActualLowerUSSecondRowCoefficients

/-!
Author: GPT-6.1 Sol, author support only.
Before-code: ../lower-r-z-gain-pair-upfront.md.
Concrete forward and true-adjoint high endpoints for the SAME actual G/E gains.
All norm constants are produced internally by the selected room budgets.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstAngularGainPair
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows ActualMixedAngularPairedGains ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "NegHi" => SphereSobolev (-(3/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma pairing_high_negative_inclusion (u : Hi) (z : Neg) :
    PP (IH u) z = sphereSobolevDualPairing (3/2 : ℝ) u (I33 z) := by
  rw [sphereSobolevDualPairing_eq_tsum,sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  simp only [sphereSobolevCoefficientL_inclusion]

private lemma negative_graph (A : Half →L[ℝ] Neg) (w : Half) (b c : Neg)
    (h : A w=b-c) : A (-w)=c-b := by
  calc
    A (-w) = -(A w) := map_neg A w
    _ = -(b-c) := congrArg (fun z : Neg => -z) h
    _ = c-b := by abel

private lemma highMap_norm_neg (A : Hi →L[ℝ] Half) : ‖-A‖=‖A‖ := norm_neg A

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q


local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PL" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => pairedRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Actual finite generator's sphere-adjoint high map. -/
def firstAngularSharpHigh : FirstAngularIndex → Hi →L[ℝ] Half
  | Sum.inl V => generatorHigh V
  | Sum.inr b => raisingHigh hF hO hD b

def firstAngularSharpLow : FirstAngularIndex → Half →L[ℝ] Neg
  | Sum.inl V => generatorLow V
  | Sum.inr b => raisingLow hF hO hD b

/-- The actual G/E gained high endpoint on the caller's retained germs. -/
def firstAngularGainHigh (mixed : MRoom) (j : Fin 3) (t : Tpar) :
    FirstAngularIndex → Hi →L[ℝ] Half
  | Sum.inl V => PL hreg data.δ0 data.germs V j t
  | Sum.inr b => CH hreg mixed.G data.δ0 data.germs b j t

/-- TRUE sphere-adjoint high endpoint: pairedRightHigh, respectively minus HH. -/
def firstAngularGainSharpHigh (j : Fin 3) (t : Tpar) :
    FirstAngularIndex → Hi →L[ℝ] Half
  | Sum.inl V => PR hreg data.δ0 data.germs V j t
  | Sum.inr b => -(HH hreg data.δ0 data.germs b j t)

local notation "GH" => firstAngularGainHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GS" => firstAngularGainSharpHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Literal forward graph; the lowering and generator cases use their own
already selected actual gain diagrams. -/
theorem firstAngularGainHigh_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (v : FirstAngularIndex) (u : Hi) :
    JL (GH mixed j t v u) =
      firstAngularLow hF hO hD v (EH j t u)-EL j t (firstAngularHigh hF hO hD v u) := by
  cases v with
  | inl V => exact gen.highGraph V j t htG u
  | inr b => exact (mixed.graphs b j t htM).1 u

/-- The exact reverse bracket for the actual sphere-adjoint high endpoint. -/
theorem firstAngularGainSharpHigh_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (v : FirstAngularIndex) (u : Hi) :
    JL (GS j t v u) =
      eL j t (firstAngularSharpHigh hF hO hD v u)-
        firstAngularSharpLow hF hO hD v (eH j t u) := by
  cases v with
  | inl V => exact gen.partnerGraph V j t htG u
  | inr b =>
    have hh : JL (HH hreg data.δ0 data.germs b j t u) =
        raisingLow hF hO hD b (eH j t u)-eL j t (raisingHigh hF hO hD b u) :=
      (mixed.graphs b j t htM).2.1 u
    change JL (-(HH hreg data.δ0 data.germs b j t u)) =
      eL j t (raisingHigh hF hO hD b u)-raisingLow hF hO hD b (eH j t u)
    exact negative_graph JL (HH hreg data.δ0 data.germs b j t u)
      (raisingLow hF hO hD b (eH j t u)) (eL j t (raisingHigh hF hO hD b u)) hh

/-- The selected lower-transpose diagram identifies the true gain adjoint
against EVERY Half input, not merely two high lifts. -/
theorem firstAngularGain_low_pairing (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (v : FirstAngularIndex) (u : Hi) (z : Half) :
    PP (IH u) (GL mixed δ gen j t v z) = PP (GS j t v u) (JL z) := by
  have hLow : ContinuousLinearMap.comp I33 (GL mixed δ gen j t v) = (v016TransposeL (GS j t v)).comp JL := by
    cases v with
    | inl V => exact gen.lower V j t htG
    | inr b => exact (mixed.graphs b j t htM).2.2.2
  calc
    _ = sphereSobolevDualPairing (3/2 : ℝ) u (I33 (GL mixed δ gen j t v z)) :=
      pairing_high_negative_inclusion u _
    _ = sphereSobolevDualPairing (3/2 : ℝ) u (v016TransposeL (GS j t v) (JL z)) :=
      congrArg (fun a : NegHi => sphereSobolevDualPairing (3/2 : ℝ) u a)
        (congrArg (fun A : Half →L[ℝ] NegHi => A z) hLow)
    _ = _ := v016TransposeL_pairing _ _ _

/-- One internally produced budget precedes all parameters and all indices;
it includes the TRUE adjoint high endpoint needed in quadratic J words. -/
theorem exists_firstAngularGain_pair_cap (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ ParamRoom δ, t ∈ ParamRoom mixed.δ →
      ∀ j : Fin 3, ∀ v : FirstAngularIndex,
      ‖GH mixed j t v‖ ≤ M ∧ ‖GS j t v‖ ≤ M ∧ ‖GL mixed δ gen j t v‖ ≤ M := by
  obtain ⟨MG,hMG,hG⟩ := gen.finiteCaps 0
  obtain ⟨MM,hMM,hM⟩ := mixed.joint_caps 0
  refine ⟨1+MG+MM,by linarith,?_⟩
  intro t htG htM j v
  cases v with
  | inl V =>
    have hh := hG V j 0 (le_refl 0) t htG
    simp only [norm_iteratedFDerivWithin_zero] at hh
    exact ⟨hh.1.trans (by linarith),hh.2.1.trans (by linarith),hh.2.2.trans (by linarith)⟩
  | inr b =>
    have hh := hM b j 0 (le_refl 0) t htM
    simp only [norm_iteratedFDerivWithin_zero] at hh
    have hs : ‖GS j t (Sum.inr b)‖ ≤ MM := by
      have hNorm : ‖-(HH hreg data.δ0 data.germs b j t : Hi →L[ℝ] Half)‖ =
          ‖(HH hreg data.δ0 data.germs b j t : Hi →L[ℝ] Half)‖ :=
        highMap_norm_neg (HH hreg data.δ0 data.germs b j t)
      exact hNorm.le.trans hh.2.1
    exact ⟨hh.1.trans (by linarith),hs.trans (by linarith),hh.2.2.trans (by linarith)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstAngularGainPair
